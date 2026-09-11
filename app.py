#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
================================================================================
  RailVPS Pro  —  Complete single-file Virtual Private Server for RENDER.COM
================================================================================

  Real VPS features implemented in ONE python file:

    AUTH          • multi-user login (salted SHA-256)
                  • persistent users in /var/data/users.json
                  • role-based (admin / user)

    SHELL         • TRUE PTY shell per session (interactive bash)
                  • xterm.js frontend — full ANSI/color/cursor/tab support
                  • multiple concurrent sessions, window resize
                  • persistent working dir + history

    FILES         • browse / upload / download / edit / rename
                  • create file/folder, delete, copy, move, chmod
                  • search by name / content / regex
                  • zip / tar / gz extract & create
                  • disk usage tree, file stat, path sandbox

    PROCESSES     • live list with cpu/mem per process
                  • signals: HUP / TERM / KILL / INT / STOP / CONT
                  • process tree view

    SYSTEM        • CPU per-core, RAM, swap, disk, net, load, uptime
                  • mounts, interfaces, kernel, python, arch

    SERVICES      • environment viewer/editor
                  • pip package manager (install / uninstall / list)
                  • log viewer (system + custom)
                  • interval scheduler with output capture

    NETWORK       • ping / DNS / HTTP fetch / public IP
                  • listening ports, interfaces

    HOSTING       • multi-site static hosting  → /s/<name>/
                  • SPA fallback, custom index, custom headers

    BACKUP        • tar.gz snapshots of files + config
                  • list / download / restore / delete

    UI            • dark terminal-styled responsive SPA
                  • live stats, toasts, modals
                  • Ctrl+K terminal focus, Ctrl+S save

  ═══════════════════════════════════════════════════════════════════════════════
  DEPLOY ON RENDER.COM
  ═══════════════════════════════════════════════════════════════════════════════

  Requirements (requirements.txt):
      flask>=3.0.0
      psutil>=5.9.0
      gunicorn>=21.2.0

  Start command:
      gunicorn -w 1 --threads 32 --timeout 0 --keep-alive 75 -b 0.0.0.0:$PORT app:app

  Env vars:
      SECRET_KEY       long random string
      VPS_USERNAME     admin
      VPS_PASSWORD     <strong password>
      DATA_DIR         /var/data   (or /tmp/vpsdata on free tier)
      PYTHON_VERSION   3.11.9

================================================================================
"""

# ==============================================================================
#  IMPORTS
# ==============================================================================
import os, sys, io, json, time, pty, select, signal, struct, fcntl, termios
import threading, queue, shutil, zipfile, tarfile, secrets, hashlib, subprocess
import platform, mimetypes, sqlite3, logging, re, socket, base64, uuid
import urllib.request, urllib.parse, urllib.error
from pathlib import Path
from datetime import datetime, timedelta
from functools import wraps
from collections import deque

try:
    import psutil
except ImportError:
    psutil = None

from flask import (
    Flask, request, jsonify, send_file, session, redirect, Response,
    abort, stream_with_context, g
)

# ==============================================================================
#  CONFIG
# ==============================================================================
APP_NAME   = "RailVPS Pro"
VERSION    = "2.0.0"

SECRET_KEY  = os.environ.get("SECRET_KEY", secrets.token_hex(32))
MAX_UPLOAD  = int(os.environ.get("MAX_UPLOAD_MB", "1024")) * 1024 * 1024
CMD_TIMEOUT = int(os.environ.get("CMD_TIMEOUT", "60"))

IS_RENDER = (os.environ.get("RENDER") == "true"
             or "RENDER_SERVICE_NAME" in os.environ
             or "RENDER_EXTERNAL_URL" in os.environ)


def _pick_data_dir() -> Path:
    env = os.environ.get("DATA_DIR")
    if env:
        p = Path(env)
        try:
            p.mkdir(parents=True, exist_ok=True)
            if os.access(str(p), os.W_OK):
                return p
        except Exception:
            pass
    for cand in ("/var/data", "/data"):
        p = Path(cand)
        if p.is_dir() and os.access(str(p), os.W_OK):
            return p
    p = Path(__file__).resolve().parent / "vps_data"
    p.mkdir(parents=True, exist_ok=True)
    return p


DATA_DIR   = _pick_data_dir()
FILES_DIR  = DATA_DIR / "files"
SITES_FILE = DATA_DIR / "sites.json"
USERS_FILE = DATA_DIR / "users.json"
CRON_FILE  = DATA_DIR / "cron.json"
ENV_FILE   = DATA_DIR / "env.json"
BACKUP_DIR = DATA_DIR / "backups"
LOGS_DIR   = DATA_DIR / "logs"
for d in (FILES_DIR, BACKUP_DIR, LOGS_DIR):
    d.mkdir(parents=True, exist_ok=True)

EPHEMERAL_DATA = (str(DATA_DIR).startswith(str(Path(__file__).resolve().parent))
                  or str(DATA_DIR) in ("/tmp", "/var/tmp"))

USING_DEFAULT_PASSWORD = False

# ==============================================================================
#  APP
# ==============================================================================
app = Flask(__name__)
app.secret_key = SECRET_KEY
app.config["MAX_CONTENT_LENGTH"] = MAX_UPLOAD
app.config["SESSION_COOKIE_SAMESITE"] = "Lax"
app.config["PERMANENT_SESSION_LIFETIME"] = timedelta(days=14)

try:
    from werkzeug.middleware.proxy_fix import ProxyFix
    app.wsgi_app = ProxyFix(app.wsgi_app, x_for=1, x_proto=1, x_host=1, x_prefix=0)
except Exception:
    pass

# ==============================================================================
#  USER STORE
# ==============================================================================
def _hash(password: str, salt: str = None):
    salt = salt or secrets.token_hex(16)
    h = hashlib.sha256((salt + password).encode()).hexdigest()
    return f"{salt}${h}"

def _verify(password: str, stored: str) -> bool:
    try:
        salt, h = stored.split("$", 1)
        return secrets.compare_digest(hashlib.sha256((salt + password).encode()).hexdigest(), h)
    except Exception:
        return False

def load_users() -> dict:
    global USING_DEFAULT_PASSWORD
    if USERS_FILE.exists():
        try:
            return json.loads(USERS_FILE.read_text("utf-8"))
        except Exception:
            pass
    u = os.environ.get("VPS_USERNAME", "admin")
    p = os.environ.get("VPS_PASSWORD")
    if not p:
        p = "railway"
        USING_DEFAULT_PASSWORD = True
    users = {u: {"password": _hash(p), "role": "admin", "created": time.time()}}
    USERS_FILE.write_text(json.dumps(users, indent=2), "utf-8")
    return users

def save_users(d: dict):
    USERS_FILE.write_text(json.dumps(d, indent=2), "utf-8")

# ==============================================================================
#  HELPERS
# ==============================================================================
def login_required(f):
    @wraps(f)
    def w(*a, **kw):
        if not session.get("auth"):
            if request.path.startswith("/api/"):
                return jsonify({"ok": False, "error": "unauthorized"}), 401
            return redirect("/login")
        return f(*a, **kw)
    return w

def admin_required(f):
    @wraps(f)
    def w(*a, **kw):
        if not session.get("auth"):
            return jsonify({"ok": False, "error": "unauthorized"}), 401
        if session.get("role") != "admin":
            return jsonify({"ok": False, "error": "forbidden"}), 403
        return f(*a, **kw)
    return w

def ok(**kw): kw.setdefault("ok", True); return jsonify(kw)
def fail(msg, code=400): return jsonify({"ok": False, "error": str(msg)}), code

def human_size(n):
    if n is None: return "0 B"
    try: n = float(n)
    except Exception: return "0 B"
    for u in ("B","KB","MB","GB","TB","PB"):
        if abs(n) < 1024: return f"{n:.0f} {u}" if u == "B" else f"{n:.1f} {u}"
        n /= 1024.0
    return f"{n:.1f} EB"

def safe_join(base: Path, rel: str) -> Path:
    rel = (rel or "").replace("\\", "/").strip()
    while rel.startswith("/"): rel = rel[1:]
    parts = [p for p in rel.split("/") if p not in ("", ".", "..")]
    target = base.joinpath(*parts).resolve()
    base_r = base.resolve()
    if target != base_r and base_r not in target.parents:
        raise ValueError("Path escapes root")
    return target

def user_path(rel=""): return safe_join(FILES_DIR, rel)

def rel_of(p: Path):
    try: return "/" + str(p.resolve().relative_to(FILES_DIR.resolve())).replace("\\", "/")
    except Exception: return "/"

def jload(p: Path, default):
    if p.exists():
        try: return json.loads(p.read_text("utf-8"))
        except Exception: return default
    return default

def jsave(p: Path, data):
    p.write_text(json.dumps(data, indent=2), "utf-8")

def is_text_file(p: Path, sniff=8192) -> bool:
    try: chunk = p.open("rb").read(sniff)
    except Exception: return False
    if b"\x00" in chunk: return False
    try: chunk.decode("utf-8"); return True
    except UnicodeDecodeError: return False

# ==============================================================================
#  PTY SHELL MANAGER
# ==============================================================================
class ShellSession:
    """A real interactive PTY bash session."""
    def __init__(self, sid: str):
        self.sid = sid
        self.master, slave = pty.openpty()
        env = os.environ.copy()
        env.update({
            "TERM": "xterm-256color",
            "HOME": str(FILES_DIR),
            "PS1": r"\[\e[32m\]\u@vps\[\e[0m\]:\[\e[34m\]\w\[\e[0m\]\$ ",
            "LANG": "C.UTF-8",
            "VPS": "1",
        })
        shell = shutil.which("bash") or shutil.which("sh") or "/bin/sh"
        try:
            self.proc = subprocess.Popen(
                [shell, "-i"],
                stdin=slave, stdout=slave, stderr=slave,
                preexec_fn=os.setsid,
                env=env,
                cwd=str(FILES_DIR),
                close_fds=True,
            )
        finally:
            try: os.close(slave)
            except Exception: pass

        self.buf = deque()
        self.lock = threading.Lock()
        self.alive = True
        self.created = time.time()
        threading.Thread(target=self._reader, daemon=True).start()

    def _reader(self):
        while self.alive:
            try:
                r, _, _ = select.select([self.master], [], [], 0.5)
                if r:
                    data = os.read(self.master, 65536)
                    if not data: break
                    with self.lock:
                        self.buf.append(data)
            except OSError:
                break
            except Exception:
                break
        self.alive = False

    def write(self, data: str):
        if not self.alive: return
        try:
            os.write(self.master, data.encode("utf-8", errors="ignore"))
        except OSError:
            self.alive = False

    def read(self) -> bytes:
        with self.lock:
            if not self.buf: return b""
            data = b"".join(self.buf); self.buf.clear()
            return data

    def resize(self, rows, cols):
        try:
            fcntl.ioctl(self.master, termios.TIOCSWINSZ,
                        struct.pack("HHHH", rows, cols, 0, 0))
        except Exception: pass

    def kill(self):
        self.alive = False
        try: os.killpg(os.getpgid(self.proc.pid), signal.SIGKILL)
        except Exception:
            try: self.proc.kill()
            except Exception: pass
        try: os.close(self.master)
        except Exception: pass


_SHELLS = {}
_SHELLS_LOCK = threading.Lock()
SHELL_TTL = 3600

def shell_get(sid: str) -> ShellSession:
    with _SHELLS_LOCK:
        s = _SHELLS.get(sid)
        if s and s.alive: return s
        if s: s.kill()
        s = ShellSession(sid)
        _SHELLS[sid] = s
        return s

def shell_drop(sid: str):
    with _SHELLS_LOCK:
        s = _SHELLS.pop(sid, None)
        if s: s.kill()

def shell_reaper():
    while True:
        time.sleep(120)
        now = time.time()
        with _SHELLS_LOCK:
            dead = [k for k, v in _SHELLS.items() if not v.alive or now - v.created > SHELL_TTL]
            for k in dead:
                try: _SHELLS[k].kill()
                except Exception: pass
                _SHELLS.pop(k, None)

threading.Thread(target=shell_reaper, daemon=True).start()

# ==============================================================================
#  AUTH ROUTES
# ==============================================================================
@app.route("/login", methods=["GET", "POST"])
def login():
    if request.method == "POST":
        d = request.get_json(silent=True) or request.form
        u = (d.get("username") or "").strip()
        p = d.get("password") or ""
        users = load_users()
        user = users.get(u)
        if user and _verify(p, user["password"]):
            session.permanent = True
            session["auth"] = True
            session["user"] = u
            session["role"] = user.get("role", "user")
            return ok(redirect="/")
        return fail("Invalid credentials", 401)
    return Response(LOGIN_HTML, mimetype="text/html")

@app.route("/logout")
def logout():
    sid = session.get("shell_id")
    if sid: shell_drop(sid)
    session.clear()
    return redirect("/login")

@app.route("/healthz")
def healthz():
    return jsonify({
        "status": "ok",
        "app": APP_NAME,
        "version": VERSION,
        "on_render": IS_RENDER,
        "data_dir": str(DATA_DIR),
        "ephemeral": EPHEMERAL_DATA,
    })

# ==============================================================================
#  SYSTEM
# ==============================================================================
def _cpu_pct():
    if not psutil: return 0.0
    try: return psutil.cpu_percent(interval=None)
    except Exception: return 0.0

@app.route("/api/stats")
@login_required
def api_stats():
    data = {
        "app": APP_NAME, "version": VERSION,
        "hostname": platform.node(),
        "platform": f"{platform.system()} {platform.release()}",
        "arch": platform.machine(),
        "python": platform.python_version(),
        "time_epoch": time.time(),
        "data_dir": str(DATA_DIR),
        "ephemeral": EPHEMERAL_DATA,
        "on_render": IS_RENDER,
    }
    if psutil:
        vm = psutil.virtual_memory()
        try: du = psutil.disk_usage(str(DATA_DIR))
        except Exception: du = None
        try: net = psutil.net_io_counters()
        except Exception: net = None
        try: boot = psutil.boot_time()
        except Exception: boot = time.time()
        try:
            swap = psutil.swap_memory()
            swap_d = {"total": swap.total, "used": swap.used, "percent": swap.percent,
                      "total_h": human_size(swap.total), "used_h": human_size(swap.used)}
        except Exception:
            swap_d = None

        data.update({
            "cpu": {
                "percent": _cpu_pct(),
                "cores": psutil.cpu_count(logical=True),
                "physical": psutil.cpu_count(logical=False),
                "per_core": (psutil.cpu_percent(percpu=True) if hasattr(psutil, "cpu_percent") else []),
                "load": list(os.getloadavg()) if hasattr(os, "getloadavg") else [0,0,0],
            },
            "memory": {
                "total": vm.total, "used": vm.used, "free": vm.available, "percent": vm.percent,
                "total_h": human_size(vm.total), "used_h": human_size(vm.used),
                "free_h": human_size(vm.available),
            },
            "swap": swap_d,
            "disk": ({
                "total": du.total, "used": du.used, "free": du.free, "percent": du.percent,
                "total_h": human_size(du.total), "used_h": human_size(du.used),
                "free_h": human_size(du.free),
            } if du else None),
            "network": ({
                "sent": net.bytes_sent, "recv": net.bytes_recv,
                "sent_h": human_size(net.bytes_sent), "recv_h": human_size(net.bytes_recv),
                "packets_sent": net.packets_sent, "packets_recv": net.packets_recv,
            } if net else None),
            "uptime": time.time() - boot, "boot_time": boot,
            "processes": len(psutil.pids()),
        })
    total = 0; count = 0
    for root, _dirs, files in os.walk(FILES_DIR):
        for f in files:
            try: total += os.path.getsize(os.path.join(root, f)); count += 1
            except OSError: pass
    data["storage"] = {"bytes": total, "human": human_size(total), "files": count}
    return jsonify(data)


@app.route("/api/system/info")
@login_required
def api_system_info():
    info = {
        "hostname": platform.node(),
        "system": platform.system(),
        "release": platform.release(),
        "version": platform.version(),
        "machine": platform.machine(),
        "processor": platform.processor(),
        "python": sys.version,
        "python_exe": sys.executable,
        "cwd": os.getcwd(),
        "pid": os.getpid(),
        "ppid": os.getppid(),
        "user": os.environ.get("USER") or os.environ.get("USERNAME") or "root",
        "uname": list(os.uname()) if hasattr(os, "uname") else [],
        "env_count": len(os.environ),
        "on_render": IS_RENDER,
        "data_dir": str(DATA_DIR),
        "ephemeral": EPHEMERAL_DATA,
    }
    if IS_RENDER:
        info["render"] = {
            "service_name": os.environ.get("RENDER_SERVICE_NAME"),
            "service_type": os.environ.get("RENDER_SERVICE_TYPE"),
            "external_url": os.environ.get("RENDER_EXTERNAL_URL"),
            "instance_id":  os.environ.get("RENDER_INSTANCE_ID"),
            "region":       os.environ.get("RENDER_REGION"),
        }
    if psutil:
        try:
            info["mounts"] = [{
                "device": p.device, "mountpoint": p.mountpoint,
                "fstype": p.fstype, "opts": p.opts,
            } for p in psutil.disk_partitions(all=False)]
        except Exception:
            info["mounts"] = []
        try:
            info["interfaces"] = {
                name: [a.address for a in addrs if a.family == socket.AF_INET]
                for name, addrs in psutil.net_if_addrs().items()
            }
        except Exception:
            info["interfaces"] = {}
    return jsonify(info)


@app.route("/api/system/env", methods=["GET", "POST"])
@login_required
def api_env():
    if request.method == "POST":
        d = request.get_json(silent=True) or {}
        custom = jload(ENV_FILE, {})
        if "delete" in d:
            custom.pop(d["delete"], None)
        elif "key" in d:
            custom[d["key"]] = d.get("value", "")
        jsave(ENV_FILE, custom)
        return ok()
    sensitive = re.compile(r"(password|secret|token|key|auth|private)", re.I)
    current = {}
    for k, v in os.environ.items():
        current[k] = "***" if sensitive.search(k) else v
    return jsonify({"system": current, "custom": jload(ENV_FILE, {})})

# ==============================================================================
#  PROCESSES
# ==============================================================================
@app.route("/api/processes")
@login_required
def api_processes():
    if not psutil: return jsonify({"processes": []})
    procs = []
    for p in psutil.process_iter(["pid", "ppid", "name", "username", "memory_percent",
                                  "cpu_percent", "status", "create_time", "cmdline"]):
        try:
            i = p.info
            procs.append({
                "pid": i["pid"], "ppid": i.get("ppid"),
                "name": i.get("name"),
                "user": i.get("username"),
                "mem": round(i.get("memory_percent") or 0, 2),
                "cpu": round(i.get("cpu_percent") or 0, 1),
                "status": i.get("status"),
                "started": i.get("create_time"),
                "cmd": " ".join(i.get("cmdline") or [])[:200],
            })
        except Exception:
            continue
    procs.sort(key=lambda x: (x["cpu"], x["mem"]), reverse=True)
    return jsonify({"processes": procs[:200]})


@app.route("/api/process/kill", methods=["POST"])
@login_required
def api_process_kill():
    if not psutil: return fail("psutil not installed")
    d = request.get_json(silent=True) or {}
    pid = int(d.get("pid", 0))
    sig = d.get("signal", "TERM").upper()
    if pid <= 1: return fail("Refusing to kill PID %s" % pid)
    sigmap = {"TERM": signal.SIGTERM, "KILL": signal.SIGKILL,
              "INT": signal.SIGINT, "HUP": signal.SIGHUP, "STOP": signal.SIGSTOP,
              "CONT": signal.SIGCONT}
    if sig not in sigmap: return fail("Bad signal")
    try:
        os.kill(pid, sigmap[sig])
        return ok(message=f"Sent SIG{sig} to {pid}")
    except Exception as e:
        return fail(e)


@app.route("/api/process/tree")
@login_required
def api_process_tree():
    if not psutil: return jsonify({"tree": []})
    procs = {}
    for p in psutil.process_iter(["pid", "ppid", "name"]):
        try:
            i = p.info
            procs[i["pid"]] = {"pid": i["pid"], "ppid": i.get("ppid") or 0,
                               "name": i.get("name"), "children": []}
        except Exception: pass
    roots = []
    for pid, node in procs.items():
        pp = node["ppid"]
        if pp in procs and pp != pid:
            procs[pp]["children"].append(node)
        else:
            roots.append(node)
    return jsonify({"tree": roots})

# ==============================================================================
#  FILES
# ==============================================================================
@app.route("/api/files")
@login_required
def api_files():
    rel = request.args.get("path", "/")
    try: target = user_path(rel)
    except ValueError as e: return fail(e)
    if not target.exists(): return fail("Not found", 404)
    if not target.is_dir(): return fail("Not a directory")

    entries = []
    for entry in os.scandir(target):
        try:
            st = entry.stat()
            is_dir = entry.is_dir()
            entries.append({
                "name": entry.name,
                "path": rel_of(Path(entry.path)),
                "dir": is_dir,
                "size": 0 if is_dir else st.st_size,
                "size_h": "" if is_dir else human_size(st.st_size),
                "mtime": st.st_mtime,
                "mtime_h": datetime.fromtimestamp(st.st_mtime).strftime("%Y-%m-%d %H:%M"),
                "mode": oct(st.st_mode & 0o777),
                "ext": "" if is_dir else Path(entry.name).suffix.lower().lstrip("."),
                "text": (not is_dir) and st.st_size < 2_000_000 and is_text_file(Path(entry.path)),
                "symlink": entry.is_symlink(),
            })
        except OSError:
            continue
    entries.sort(key=lambda x: (not x["dir"], x["name"].lower()))
    parent = None
    if rel not in ("/", "", None):
        parent = rel_of(target.parent)
    return jsonify({
        "ok": True,
        "path": rel_of(target) if target != FILES_DIR else "/",
        "parent": parent,
        "entries": entries,
        "count": len(entries),
    })


@app.route("/api/file")
@login_required
def api_file_read():
    try: target = user_path(request.args.get("path", ""))
    except ValueError as e: return fail(e)
    if not target.is_file(): return fail("Not a file", 404)
    if target.stat().st_size > 5*1024*1024: return fail("File too large (max 5 MB)")
    try: content = target.read_text("utf-8", errors="replace")
    except Exception as e: return fail(e)
    return jsonify({"ok": True, "path": rel_of(target), "content": content,
                    "size": target.stat().st_size})


@app.route("/api/file/save", methods=["POST"])
@login_required
def api_file_save():
    d = request.get_json(silent=True) or {}
    try: target = user_path(d.get("path", ""))
    except ValueError as e: return fail(e)
    if target.is_dir(): return fail("Path is a directory")
    try:
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(d.get("content", ""), "utf-8")
        return ok(path=rel_of(target))
    except Exception as e: return fail(e)


@app.route("/api/file/new", methods=["POST"])
@login_required
def api_file_new():
    d = request.get_json(silent=True) or {}
    try: target = user_path(d.get("path", ""))
    except ValueError as e: return fail(e)
    if target.exists(): return fail("Already exists")
    try:
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text("", "utf-8")
        return ok(path=rel_of(target))
    except Exception as e: return fail(e)


@app.route("/api/file/mkdir", methods=["POST"])
@login_required
def api_mkdir():
    d = request.get_json(silent=True) or {}
    try: target = user_path(d.get("path", ""))
    except ValueError as e: return fail(e)
    try:
        target.mkdir(parents=True, exist_ok=True)
        return ok(path=rel_of(target))
    except Exception as e: return fail(e)


@app.route("/api/file/rename", methods=["POST"])
@login_required
def api_rename():
    d = request.get_json(silent=True) or {}
    newname = (d.get("newname") or "").strip().replace("/", "")
    if not newname: return fail("Invalid name")
    try: target = user_path(d.get("path", ""))
    except ValueError as e: return fail(e)
    if not target.exists(): return fail("Not found", 404)
    dest = target.parent / newname
    if dest.exists(): return fail("Already exists")
    try:
        target.rename(dest); return ok(path=rel_of(dest))
    except Exception as e: return fail(e)


@app.route("/api/file/copy", methods=["POST"])
@login_required
def api_copy():
    d = request.get_json(silent=True) or {}
    try:
        src = user_path(d.get("src", "")); dst = user_path(d.get("dst", ""))
    except ValueError as e: return fail(e)
    if not src.exists(): return fail("Source not found", 404)
    if dst.exists() and not d.get("overwrite"): return fail("Destination exists")
    try:
        if src.is_dir():
            shutil.copytree(src, dst, dirs_exist_ok=True)
        else:
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(src, dst)
        return ok()
    except Exception as e: return fail(e)


@app.route("/api/file/move", methods=["POST"])
@login_required
def api_move():
    d = request.get_json(silent=True) or {}
    try:
        src = user_path(d.get("src", "")); dst = user_path(d.get("dst", ""))
    except ValueError as e: return fail(e)
    if not src.exists(): return fail("Source not found", 404)
    if dst.exists() and not d.get("overwrite"): return fail("Destination exists")
    try:
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.move(str(src), str(dst))
        return ok()
    except Exception as e: return fail(e)


@app.route("/api/file/chmod", methods=["POST"])
@login_required
def api_chmod():
    d = request.get_json(silent=True) or {}
    mode = (d.get("mode") or "").strip()
    if not re.fullmatch(r"[0-7]{3,4}", mode): return fail("Invalid mode (e.g. 644, 755)")
    try: target = user_path(d.get("path", ""))
    except ValueError as e: return fail(e)
    if not target.exists(): return fail("Not found", 404)
    try:
        os.chmod(target, int(mode, 8))
        return ok()
    except Exception as e: return fail(e)


@app.route("/api/file/delete", methods=["POST"])
@login_required
def api_delete():
    d = request.get_json(silent=True) or {}
    paths = d.get("paths") or ([d["path"]] if d.get("path") else [])
    if not paths: return fail("No paths")
    removed, errors = [], []
    for p in paths:
        try:
            t = user_path(p)
            if t == FILES_DIR:
                errors.append(f"{p}: refusing to delete root"); continue
            if t.is_dir() and not t.is_symlink(): shutil.rmtree(t)
            elif t.exists() or t.is_symlink(): t.unlink()
            else: errors.append(f"{p}: not found"); continue
            removed.append(p)
        except Exception as e: errors.append(f"{p}: {e}")
    return jsonify({"ok": True, "removed": removed, "errors": errors})


def _sanitize_upload_name(name: str) -> str:
    name = (name or "").replace("\\", "/")
    parts = [p for p in name.split("/") if p not in ("", ".", "..")]
    return "/".join(parts) or "unnamed"


@app.route("/api/file/upload", methods=["POST"])
@login_required
def api_upload():
    base_rel = request.form.get("path", "/")
    try: base = user_path(base_rel)
    except ValueError as e: return fail(e)
    if not base.is_dir(): return fail("Destination is not a directory")
    files = request.files.getlist("files") or request.files.getlist("file")
    if not files: return fail("No files received")
    saved = []
    for f in files:
        safe = _sanitize_upload_name(f.filename)
        dest = base / safe
        try:
            dest.parent.mkdir(parents=True, exist_ok=True)
            f.save(str(dest))
            sz = dest.stat().st_size
            saved.append({"name": safe, "size": sz, "size_h": human_size(sz)})
        except Exception as e:
            saved.append({"name": safe, "error": str(e)})
    return jsonify({"ok": True, "saved": saved, "count": len(saved)})


@app.route("/api/file/download")
@login_required
def api_download():
    try: t = user_path(request.args.get("path", ""))
    except ValueError as e: return fail(e)
    if not t.is_file(): return fail("Not found", 404)
    return send_file(str(t), as_attachment=True, download_name=t.name)


@app.route("/api/file/zip")
@login_required
def api_zip():
    try: t = user_path(request.args.get("path", ""))
    except ValueError as e: return fail(e)
    if not t.exists(): return fail("Not found", 404)
    buf = io.BytesIO()
    with zipfile.ZipFile(buf, "w", zipfile.ZIP_DEFLATED) as zf:
        if t.is_file(): zf.write(str(t), t.name)
        else:
            for root, _d, files in os.walk(t):
                for fn in files:
                    full = Path(root) / fn
                    zf.write(str(full), str(full.relative_to(t.parent)))
    buf.seek(0)
    return send_file(buf, mimetype="application/zip", as_attachment=True,
                     download_name=f"{t.name or 'root'}.zip")


@app.route("/api/file/tar", methods=["POST"])
@login_required
def api_tar():
    d = request.get_json(silent=True) or {}
    try: t = user_path(d.get("path", ""))
    except ValueError as e: return fail(e)
    if not t.exists(): return fail("Not found", 404)
    buf = io.BytesIO()
    with tarfile.open(fileobj=buf, mode="w:gz") as tf:
        tf.add(str(t), arcname=t.name)
    buf.seek(0)
    return send_file(buf, mimetype="application/gzip", as_attachment=True,
                     download_name=f"{t.name or 'root'}.tar.gz")


@app.route("/api/file/extract", methods=["POST"])
@login_required
def api_extract():
    d = request.get_json(silent=True) or {}
    try: t = user_path(d.get("path", ""))
    except ValueError as e: return fail(e)
    if not t.is_file(): return fail("Not a file", 404)
    dest = t.parent
    if d.get("dest"):
        try: dest = user_path(d["dest"])
        except ValueError as e: return fail(e)
    name = t.name.lower()
    try:
        if name.endswith(".zip"):
            with zipfile.ZipFile(t) as zf:
                zf.extractall(dest)
        elif name.endswith((".tar", ".tar.gz", ".tgz", ".tar.bz2", ".tbz2", ".tar.xz", ".txz")):
            with tarfile.open(t) as tf:
                tf.extractall(dest)
        elif name.endswith(".gz"):
            out = dest / t.name[:-3]
            import gzip
            with gzip.open(t, "rb") as fi, open(out, "wb") as fo:
                shutil.copyfileobj(fi, fo)
        else:
            return fail("Unsupported archive")
        return ok(dest=rel_of(dest))
    except Exception as e:
        return fail(e)


@app.route("/api/file/search")
@login_required
def api_search():
    q = (request.args.get("q") or "").strip()
    mode = request.args.get("mode", "name")
    root = request.args.get("path", "/")
    limit = int(request.args.get("limit", 200))
    if not q: return fail("Query required")
    try: base = user_path(root)
    except ValueError as e: return fail(e)
    if not base.is_dir(): return fail("Not a directory")

    results = []
    pattern = None
    if mode == "regex":
        try: pattern = re.compile(q)
        except re.error as e: return fail(f"Bad regex: {e}")

    def visit(p: Path):
        if len(results) >= limit: return
        try:
            for entry in os.scandir(p):
                if len(results) >= limit: return
                ep = Path(entry.path)
                if entry.is_dir(follow_symlinks=False):
                    if mode == "name" and q.lower() in entry.name.lower():
                        results.append({"path": rel_of(ep), "dir": True, "size": 0, "match": "name"})
                    visit(ep)
                else:
                    matched = False
                    if mode == "name":
                        matched = q.lower() in entry.name.lower()
                    elif mode == "content":
                        try:
                            if entry.stat().st_size < 2_000_000:
                                txt = ep.read_text("utf-8", errors="ignore")
                                if q in txt: matched = True
                        except Exception: pass
                    elif mode == "regex":
                        try:
                            if entry.stat().st_size < 2_000_000:
                                txt = ep.read_text("utf-8", errors="ignore")
                                if pattern.search(txt): matched = True
                        except Exception: pass
                    if matched:
                        try: sz = entry.stat().st_size
                        except OSError: sz = 0
                        results.append({"path": rel_of(ep), "dir": False,
                                        "size": sz, "size_h": human_size(sz),
                                        "match": mode})
        except (PermissionError, OSError):
            pass
    visit(base)
    return jsonify({"ok": True, "results": results, "count": len(results)})


@app.route("/api/file/stat")
@login_required
def api_file_stat():
    try: t = user_path(request.args.get("path", ""))
    except ValueError as e: return fail(e)
    if not t.exists(): return fail("Not found", 404)
    st = t.stat()
    return jsonify({
        "path": rel_of(t), "name": t.name,
        "size": st.st_size, "size_h": human_size(st.st_size),
        "mode": oct(st.st_mode & 0o777),
        "uid": st.st_uid, "gid": st.st_gid,
        "atime": st.st_atime, "mtime": st.st_mtime, "ctime": st.st_ctime,
        "is_dir": t.is_dir(), "is_file": t.is_file(), "is_link": t.is_symlink(),
        "is_text": t.is_file() and is_text_file(t),
    })

# ==============================================================================
#  SHELL (PTY)
# ==============================================================================
@app.route("/api/shell/spawn", methods=["POST"])
@login_required
def api_shell_spawn():
    sid = session.get("shell_id")
    if not sid:
        sid = secrets.token_hex(8)
        session["shell_id"] = sid
    shell_get(sid)
    return ok(sid=sid)


@app.route("/api/shell/write", methods=["POST"])
@login_required
def api_shell_write():
    d = request.get_json(silent=True) or {}
    sid = session.get("shell_id")
    if not sid: return fail("No shell")
    shell_get(sid).write(d.get("data", ""))
    return ok()


@app.route("/api/shell/resize", methods=["POST"])
@login_required
def api_shell_resize():
    d = request.get_json(silent=True) or {}
    sid = session.get("shell_id")
    if not sid: return fail("No shell")
    shell_get(sid).resize(int(d.get("rows", 24)), int(d.get("cols", 80)))
    return ok()


@app.route("/api/shell/read")
@login_required
def api_shell_read():
    sid = session.get("shell_id")
    if not sid: return Response(b"", mimetype="application/octet-stream")
    s = shell_get(sid)
    deadline = time.time() + 20
    while time.time() < deadline:
        data = s.read()
        if data: return Response(data, mimetype="application/octet-stream")
        if not s.alive: break
        time.sleep(0.05)
    return Response(b"", mimetype="application/octet-stream")


@app.route("/api/shell/kill", methods=["POST"])
@login_required
def api_shell_kill():
    sid = session.get("shell_id")
    if sid:
        shell_drop(sid)
        session.pop("shell_id", None)
    return ok()


@app.route("/api/exec", methods=["POST"])
@login_required
def api_exec():
    d = request.get_json(silent=True) or {}
    cmd = (d.get("cmd") or "").strip()
    if not cmd: return ok(stdout="", stderr="", code=0, cwd="/", duration=0)
    try: cwd = user_path(d.get("cwd") or "/")
    except ValueError: cwd = FILES_DIR
    if not cwd.is_dir(): cwd = FILES_DIR

    env = os.environ.copy()
    env.update({"HOME": str(FILES_DIR), "PWD": str(cwd),
                "TERM": "xterm-256color", "VPS": "1"})
    started = time.time()
    try:
        proc = subprocess.run(cmd, shell=True, cwd=str(cwd), env=env,
                              capture_output=True, timeout=CMD_TIMEOUT)
        out = proc.stdout.decode("utf-8", "replace")
        err = proc.stderr.decode("utf-8", "replace")
        code = proc.returncode
    except subprocess.TimeoutExpired:
        out, err, code = "", f"Timed out after {CMD_TIMEOUT}s\n", 124
    except Exception as e:
        out, err, code = "", f"{type(e).__name__}: {e}\n", 1
    return ok(stdout=out, stderr=err, code=code,
              cwd=rel_of(cwd), duration=round(time.time() - started, 3))

# ==============================================================================
#  SITES
# ==============================================================================
@app.route("/api/sites")
@login_required
def api_sites_list():
    sites = jload(SITES_FILE, {})
    out = []
    for name, cfg in sites.items():
        base = FILES_DIR / cfg.get("dir", "")
        size = 0
        if base.exists():
            for root, _d, files in os.walk(base):
                for f in files:
                    try: size += os.path.getsize(os.path.join(root, f))
                    except OSError: pass
        out.append({
            "name": name, "dir": cfg.get("dir", ""),
            "spa": bool(cfg.get("spa")), "index": cfg.get("index", "index.html"),
            "url": f"/s/{name}/", "exists": base.exists(),
            "size_h": human_size(size), "created": cfg.get("created"),
            "headers": cfg.get("headers") or {},
        })
    out.sort(key=lambda x: x["name"])
    return jsonify({"ok": True, "sites": out})


@app.route("/api/sites", methods=["POST"])
@login_required
def api_sites_create():
    d = request.get_json(silent=True) or {}
    name = (d.get("name") or "").strip().lower()
    name = "".join(c for c in name if c.isalnum() or c in "-_")
    if not name: return fail("Invalid site name")
    directory = (d.get("dir") or name).strip().strip("/")
    try: target = user_path(directory)
    except ValueError as e: return fail(e)
    target.mkdir(parents=True, exist_ok=True)
    sites = jload(SITES_FILE, {})
    sites[name] = {
        "dir": directory,
        "spa": bool(d.get("spa")),
        "index": d.get("index") or "index.html",
        "headers": d.get("headers") or {},
        "created": time.time(),
    }
    jsave(SITES_FILE, sites)
    return ok(name=name, url=f"/s/{name}/")


@app.route("/api/sites/<name>", methods=["DELETE"])
@login_required
def api_sites_delete(name):
    sites = jload(SITES_FILE, {})
    if name not in sites: return fail("Not found", 404)
    del sites[name]; jsave(SITES_FILE, sites)
    return ok()


def _serve_site(name, sub):
    sites = jload(SITES_FILE, {})
    cfg = sites.get(name)
    if not cfg: abort(404)
    try: base = user_path(cfg.get("dir", ""))
    except ValueError: abort(403)
    if not base.is_dir(): abort(404)
    try: target = safe_join(base, sub or "")
    except ValueError: abort(403)
    if target.is_dir(): target = target / (cfg.get("index") or "index.html")
    if target.is_file():
        mime, _ = mimetypes.guess_type(str(target))
        resp = send_file(str(target), mimetype=mime)
        for k, v in (cfg.get("headers") or {}).items():
            resp.headers[k] = v
        return resp
    if cfg.get("spa"):
        fb = base / (cfg.get("index") or "index.html")
        if fb.is_file(): return send_file(str(fb))
    abort(404)


@app.route("/s/<name>/", defaults={"sub": ""})
@app.route("/s/<name>/<path:sub>")
def serve_site(name, sub): return _serve_site(name, sub)


@app.route("/raw/<path:sub>")
def serve_raw(sub):
    try: t = safe_join(FILES_DIR, sub)
    except ValueError: abort(403)
    if not t.is_file(): abort(404)
    mime, _ = mimetypes.guess_type(str(t))
    return send_file(str(t), mimetype=mime)

# ==============================================================================
#  CRON
# ==============================================================================
_cron_lock = threading.Lock()
_cron_output = {}

def _cron_runner():
    while True:
        try:
            jobs = jload(CRON_FILE, {})
            now = time.time()
            for jid, job in list(jobs.items()):
                if not job.get("enabled", True): continue
                interval = int(job.get("interval", 0))
                if interval <= 0: continue
                last = job.get("last_run", 0)
                if now - last < interval: continue
                job["last_run"] = now
                job["running"] = True
                jsave(CRON_FILE, jobs)
                threading.Thread(target=_run_cron_job,
                                 args=(jid, job.get("cmd", "")), daemon=True).start()
        except Exception:
            pass
        time.sleep(15)

def _run_cron_job(jid, cmd):
    started = time.time()
    try:
        p = subprocess.run(cmd, shell=True, cwd=str(FILES_DIR),
                           capture_output=True, timeout=600)
        out = p.stdout.decode("utf-8", "replace")
        err = p.stderr.decode("utf-8", "replace")
        code = p.returncode
    except Exception as e:
        out, err, code = "", str(e), -1
    dur = round(time.time() - started, 2)
    entry = {"time": started, "code": code, "duration": dur,
             "stdout": out[-10000:], "stderr": err[-10000:]}
    with _cron_lock:
        _cron_output.setdefault(jid, deque(maxlen=20)).appendleft(entry)
    jobs = jload(CRON_FILE, {})
    if jid in jobs:
        jobs[jid]["running"] = False
        jobs[jid]["last_code"] = code
        jobs[jid]["last_duration"] = dur
        jsave(CRON_FILE, jobs)

threading.Thread(target=_cron_runner, daemon=True).start()


@app.route("/api/cron")
@login_required
def api_cron_list():
    jobs = jload(CRON_FILE, {})
    out = []
    for jid, j in jobs.items():
        out.append({
            "id": jid, "name": j.get("name"), "cmd": j.get("cmd"),
            "interval": j.get("interval"), "enabled": j.get("enabled", True),
            "last_run": j.get("last_run"), "last_code": j.get("last_code"),
            "running": j.get("running", False),
        })
    out.sort(key=lambda x: x.get("last_run") or 0, reverse=True)
    return jsonify({"ok": True, "jobs": out})


@app.route("/api/cron", methods=["POST"])
@login_required
def api_cron_create():
    d = request.get_json(silent=True) or {}
    name = (d.get("name") or "job").strip()
    cmd = (d.get("cmd") or "").strip()
    interval = int(d.get("interval", 300))
    if not cmd: return fail("Command required")
    if interval < 10: return fail("Interval must be >= 10s")
    jid = uuid.uuid4().hex[:10]
    jobs = jload(CRON_FILE, {})
    jobs[jid] = {"name": name, "cmd": cmd, "interval": interval,
                 "enabled": True, "created": time.time()}
    jsave(CRON_FILE, jobs)
    return ok(id=jid)


@app.route("/api/cron/<jid>", methods=["DELETE"])
@login_required
def api_cron_delete(jid):
    jobs = jload(CRON_FILE, {})
    jobs.pop(jid, None); jsave(CRON_FILE, jobs)
    with _cron_lock: _cron_output.pop(jid, None)
    return ok()


@app.route("/api/cron/<jid>/toggle", methods=["POST"])
@login_required
def api_cron_toggle(jid):
    jobs = jload(CRON_FILE, {})
    if jid not in jobs: return fail("Not found", 404)
    jobs[jid]["enabled"] = not jobs[jid].get("enabled", True)
    jsave(CRON_FILE, jobs)
    return ok(enabled=jobs[jid]["enabled"])


@app.route("/api/cron/<jid>/run", methods=["POST"])
@login_required
def api_cron_run(jid):
    jobs = jload(CRON_FILE, {})
    if jid not in jobs: return fail("Not found", 404)
    threading.Thread(target=_run_cron_job,
                     args=(jid, jobs[jid].get("cmd", "")), daemon=True).start()
    return ok()


@app.route("/api/cron/<jid>/output")
@login_required
def api_cron_output(jid):
    with _cron_lock:
        runs = list(_cron_output.get(jid, []))
    return jsonify({"ok": True, "runs": runs})

# ==============================================================================
#  BACKUP
# ==============================================================================
@app.route("/api/backup/list")
@login_required
def api_backup_list():
    out = []
    for f in sorted(BACKUP_DIR.glob("*.tar.gz"),
                    key=lambda p: p.stat().st_mtime, reverse=True):
        st = f.stat()
        out.append({"name": f.name, "size": st.st_size,
                    "size_h": human_size(st.st_size), "mtime": st.st_mtime,
                    "mtime_h": datetime.fromtimestamp(st.st_mtime).strftime("%Y-%m-%d %H:%M")})
    return jsonify({"ok": True, "backups": out})


@app.route("/api/backup/create", methods=["POST"])
@login_required
def api_backup_create():
    name = f"backup_{datetime.utcnow().strftime('%Y%m%d_%H%M%S')}.tar.gz"
    out = BACKUP_DIR / name
    try:
        with tarfile.open(out, "w:gz") as tf:
            tf.add(str(FILES_DIR), arcname="files")
            for extra in (SITES_FILE, USERS_FILE, CRON_FILE, ENV_FILE):
                if extra.exists(): tf.add(str(extra), arcname=extra.name)
        return ok(name=name, size=out.stat().st_size,
                  size_h=human_size(out.stat().st_size))
    except Exception as e:
        return fail(e)


@app.route("/api/backup/download/<name>")
@login_required
def api_backup_download(name):
    p = BACKUP_DIR / os.path.basename(name)
    if not p.is_file(): return fail("Not found", 404)
    return send_file(str(p), as_attachment=True, download_name=p.name)


@app.route("/api/backup/restore", methods=["POST"])
@login_required
def api_backup_restore():
    d = request.get_json(silent=True) or {}
    name = os.path.basename(d.get("name", ""))
    p = BACKUP_DIR / name
    if not p.is_file(): return fail("Not found", 404)
    try:
        with tarfile.open(p) as tf:
            for member in tf.getmembers():
                if member.name.startswith("/") or ".." in Path(member.name).parts:
                    return fail("Unsafe archive member: " + member.name)
            tmp = DATA_DIR / "_restore_tmp"
            if tmp.exists(): shutil.rmtree(tmp)
            tmp.mkdir()
            tf.extractall(tmp)
            new_files = tmp / "files"
            if new_files.is_dir():
                shutil.rmtree(FILES_DIR); new_files.rename(FILES_DIR)
            for extra in ("sites.json", "users.json", "cron.json", "env.json"):
                ep = tmp / extra
                if ep.is_file(): shutil.copy2(ep, DATA_DIR / extra)
            shutil.rmtree(tmp, ignore_errors=True)
        return ok()
    except Exception as e:
        return fail(e)


@app.route("/api/backup/delete", methods=["POST"])
@login_required
def api_backup_delete():
    d = request.get_json(silent=True) or {}
    name = os.path.basename(d.get("name", ""))
    p = BACKUP_DIR / name
    if not p.is_file(): return fail("Not found", 404)
    try: p.unlink(); return ok()
    except Exception as e: return fail(e)

# ==============================================================================
#  LOGS
# ==============================================================================
def _list_logs():
    logs = []
    for f in LOGS_DIR.glob("*"):
        if f.is_file():
            logs.append({"name": f.name, "path": str(f), "size": f.stat().st_size})
    for cand in ("/var/log/syslog", "/var/log/messages", "/var/log/auth.log",
                 "/var/log/nginx/access.log", "/var/log/nginx/error.log"):
        p = Path(cand)
        if p.is_file() and os.access(str(p), os.R_OK):
            try: logs.append({"name": "sys:" + p.name, "path": str(p), "size": p.stat().st_size})
            except OSError: pass
    return logs


@app.route("/api/logs")
@login_required
def api_logs_list():
    return jsonify({"ok": True, "logs": _list_logs()})


@app.route("/api/logs/read")
@login_required
def api_logs_read():
    path = request.args.get("path", "")
    lines = int(request.args.get("lines", 500))
    if path.startswith("sys:"):
        p = Path("/var/log") / path[4:]
    else:
        p = LOGS_DIR / os.path.basename(path)
    if not p.is_file(): return fail("Not found", 404)
    try:
        with open(p, "rb") as f:
            f.seek(0, 2); size = f.tell()
            chunk = min(size, 200_000)
            f.seek(size - chunk)
            data = f.read().decode("utf-8", errors="replace")
        tail = "\n".join(data.splitlines()[-lines:])
        return jsonify({"ok": True, "content": tail, "size": size})
    except Exception as e:
        return fail(e)

# ==============================================================================
#  NETWORK TOOLS
# ==============================================================================
@app.route("/api/network/interfaces")
@login_required
def api_net_ifaces():
    if not psutil: return jsonify({"ok": True, "interfaces": {}})
    out = {}
    addrs = psutil.net_if_addrs()
    stats = psutil.net_if_stats()
    for name, list_ in addrs.items():
        out[name] = {
            "addresses": [{"family": str(a.family), "address": a.address,
                           "netmask": a.netmask, "broadcast": a.broadcast}
                          for a in list_],
            "up": stats[name].isup if name in stats else None,
            "speed": stats[name].speed if name in stats else None,
        }
    return jsonify({"ok": True, "interfaces": out})


@app.route("/api/network/ports")
@login_required
def api_net_ports():
    if not psutil: return jsonify({"ok": True, "listening": []})
    try: conns = psutil.net_connections(kind="inet")
    except Exception: return jsonify({"ok": True, "listening": []})
    seen = set(); out = []
    for c in conns:
        if c.status == psutil.CONN_LISTEN and c.laddr:
            key = (c.laddr.port, c.laddr.ip)
            if key in seen: continue
            seen.add(key)
            try: pname = psutil.Process(c.pid).name() if c.pid else None
            except Exception: pname = None
            out.append({"port": c.laddr.port, "ip": c.laddr.ip,
                        "pid": c.pid, "process": pname})
    out.sort(key=lambda x: x["port"])
    return jsonify({"ok": True, "listening": out})


@app.route("/api/network/ping", methods=["POST"])
@login_required
def api_net_ping():
    d = request.get_json(silent=True) or {}
    host = (d.get("host") or "").strip()
    if not re.fullmatch(r"[A-Za-z0-9\.\-_]+", host): return fail("Invalid host")
    count = int(d.get("count", 4))
    try:
        p = subprocess.run(["ping", "-c", str(count), "-W", "2", host],
                           capture_output=True, timeout=20)
        return ok(stdout=p.stdout.decode("utf-8", "replace"),
                  stderr=p.stderr.decode("utf-8", "replace"), code=p.returncode)
    except FileNotFoundError:
        return fail("ping not installed in container")
    except Exception as e:
        return fail(e)


@app.route("/api/network/dns", methods=["POST"])
@login_required
def api_net_dns():
    d = request.get_json(silent=True) or {}
    host = (d.get("host") or "").strip()
    try:
        infos = socket.getaddrinfo(host, None)
        seen = set(); out = []
        for fam, _, _, _, sa in infos:
            ip = sa[0]
            if ip in seen: continue
            seen.add(ip)
            out.append({"family": "IPv6" if fam == socket.AF_INET6 else "IPv4", "ip": ip})
        return ok(records=out)
    except Exception as e:
        return fail(e)


@app.route("/api/network/curl", methods=["POST"])
@login_required
def api_net_curl():
    d = request.get_json(silent=True) or {}
    url = (d.get("url") or "").strip()
    method = d.get("method", "GET").upper()
    if not url.startswith(("http://", "https://")): return fail("Only http(s) URLs")
    try:
        req = urllib.request.Request(url, method=method)
        for k, v in (d.get("headers") or {}).items():
            req.add_header(k, v)
        with urllib.request.urlopen(req, timeout=20) as r:
            body = r.read(200_000)
            try: text = body.decode("utf-8")
            except UnicodeDecodeError: text = body.decode("latin-1")
            return ok(status=r.status, headers=dict(r.getheaders()),
                      body=text, size=len(body))
    except urllib.error.HTTPError as e:
        try: body = e.read().decode("utf-8", "replace")
        except Exception: body = ""
        return ok(status=e.code, headers=dict(e.headers), body=body, size=len(body))
    except Exception as e:
        return fail(e)


@app.route("/api/network/publicip")
@login_required
def api_net_publicip():
    try:
        with urllib.request.urlopen("https://api.ipify.org?format=json", timeout=8) as r:
            data = json.loads(r.read().decode())
        return ok(ip=data.get("ip"))
    except Exception as e:
        return fail(e)

# ==============================================================================
#  PIP PACKAGES
# ==============================================================================
@app.route("/api/pip/list")
@login_required
def api_pip_list():
    try:
        p = subprocess.run([sys.executable, "-m", "pip", "list", "--format=json"],
                           capture_output=True, timeout=30)
        pkgs = json.loads(p.stdout.decode() or "[]")
        pkgs.sort(key=lambda x: x.get("name", "").lower())
        return jsonify({"ok": True, "packages": pkgs})
    except Exception as e:
        return fail(e)


@app.route("/api/pip/install", methods=["POST"])
@login_required
def api_pip_install():
    d = request.get_json(silent=True) or {}
    pkgs = d.get("packages") or []
    if isinstance(pkgs, str): pkgs = [pkgs]
    if not pkgs: return fail("No packages")
    try:
        p = subprocess.run([sys.executable, "-m", "pip", "install", "--no-input", *pkgs],
                           capture_output=True, timeout=300)
        return ok(stdout=p.stdout.decode("utf-8", "replace")[-8000:],
                  stderr=p.stderr.decode("utf-8", "replace")[-4000:], code=p.returncode)
    except Exception as e:
        return fail(e)


@app.route("/api/pip/uninstall", methods=["POST"])
@login_required
def api_pip_uninstall():
    d = request.get_json(silent=True) or {}
    pkgs = d.get("packages") or []
    if isinstance(pkgs, str): pkgs = [pkgs]
    if not pkgs: return fail("No packages")
    try:
        p = subprocess.run([sys.executable, "-m", "pip", "uninstall", "-y", *pkgs],
                           capture_output=True, timeout=120)
        return ok(stdout=p.stdout.decode("utf-8", "replace")[-4000:],
                  stderr=p.stderr.decode("utf-8", "replace")[-4000:], code=p.returncode)
    except Exception as e:
        return fail(e)

# ==============================================================================
#  USERS
# ==============================================================================
@app.route("/api/users")
@admin_required
def api_users_list():
    users = load_users()
    return jsonify({"ok": True, "users": [
        {"username": u, "role": v.get("role", "user"), "created": v.get("created")}
        for u, v in users.items()
    ]})


@app.route("/api/users", methods=["POST"])
@admin_required
def api_users_create():
    d = request.get_json(silent=True) or {}
    u = (d.get("username") or "").strip()
    p = d.get("password") or ""
    role = d.get("role", "user")
    if not re.fullmatch(r"[A-Za-z0-9_.\-]{2,32}", u): return fail("Invalid username")
    if len(p) < 4: return fail("Password too short (min 4)")
    users = load_users()
    if u in users: return fail("User exists")
    users[u] = {"password": _hash(p), "role": role, "created": time.time()}
    save_users(users)
    return ok()


@app.route("/api/users/<u>", methods=["DELETE"])
@admin_required
def api_users_delete(u):
    if u == session.get("user"): return fail("Cannot delete yourself")
    users = load_users()
    if u not in users: return fail("Not found", 404)
    del users[u]; save_users(users)
    return ok()


@app.route("/api/users/password", methods=["POST"])
@login_required
def api_users_password():
    d = request.get_json(silent=True) or {}
    u = session.get("user")
    old = d.get("old") or ""
    new = d.get("new") or ""
    if len(new) < 4: return fail("New password too short")
    users = load_users()
    if u not in users or not _verify(old, users[u]["password"]):
        return fail("Wrong current password")
    users[u]["password"] = _hash(new)
    save_users(users)
    return ok()

# ==============================================================================
#  UI
# ==============================================================================
@app.route("/")
@login_required
def index():
    return Response(HTML, mimetype="text/html")

# ==============================================================================
#  LOGIN PAGE
# ==============================================================================
LOGIN_HTML = r"""<!DOCTYPE html>
<html lang="en"><head>
<meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>RailVPS Pro — Sign in</title>
<style>
*{box-sizing:border-box;margin:0;padding:0}
body{min-height:100vh;display:flex;align-items:center;justify-content:center;
  background:#080b10;
  background-image:radial-gradient(circle at 20% 20%,#12253a 0,transparent 45%),
                   radial-gradient(circle at 80% 80%,#1a1430 0,transparent 45%);
  font-family:ui-monospace,Menlo,Consolas,monospace;color:#d7e0ea}
.card{width:min(400px,92vw);background:#0f1520;border:1px solid #1e2733;
  border-radius:14px;padding:34px 30px 28px;box-shadow:0 24px 70px rgba(0,0,0,.75)}
.logo{display:flex;align-items:center;gap:10px;margin-bottom:6px}
.dot{width:10px;height:10px;border-radius:50%;background:#2ecc71;
  box-shadow:0 0 12px #2ecc71;animation:p 2s infinite}
@keyframes p{50%{opacity:.35}}
h1{font-size:19px;letter-spacing:.5px}
.sub{color:#6d7c8e;font-size:11.5px;margin-bottom:26px}
label{display:block;font-size:11px;color:#7d8b9c;margin:14px 0 6px;
  text-transform:uppercase;letter-spacing:1px}
input{width:100%;padding:11px 13px;background:#0a0f17;border:1px solid #1e2733;
  border-radius:8px;color:#d7e0ea;font:inherit;font-size:13.5px;outline:none;
  transition:border-color .15s,box-shadow .15s}
input:focus{border-color:#3ea6ff;box-shadow:0 0 0 3px rgba(62,166,255,.14)}
button{width:100%;margin-top:24px;padding:12px;border:0;border-radius:8px;cursor:pointer;
  background:linear-gradient(180deg,#3ea6ff,#1f7fe0);color:#fff;font:inherit;
  font-size:13.5px;font-weight:600;letter-spacing:.4px}
button:hover{filter:brightness(1.12)}
.err{color:#ff6b6b;font-size:12px;margin-top:14px;min-height:16px}
.foot{margin-top:22px;font-size:10.5px;color:#4a5768;text-align:center}
</style></head><body>
<form class="card" id="f">
  <div class="logo"><span class="dot"></span><h1>RailVPS Pro</h1></div>
  <div class="sub">Virtual Private Server · Control Panel v2.0</div>
  <label>Username</label><input id="u" autofocus required>
  <label>Password</label><input id="p" type="password" required>
  <button type="submit">Authenticate</button>
  <div class="err" id="e"></div>
  <div class="foot">authorized access only · all sessions logged</div>
</form>
<script>
const f=document.getElementById('f');
f.addEventListener('submit',async ev=>{
  ev.preventDefault();
  const e=document.getElementById('e');e.textContent='';
  try{
    const r=await fetch('/login',{method:'POST',
      headers:{'Content-Type':'application/json'},
      body:JSON.stringify({username:u.value,password:p.value})});
    const j=await r.json();
    if(j.ok)location.href=j.redirect||'/';
    else e.textContent=j.error||'Login failed';
  }catch(x){e.textContent='Network error';}
});
</script></body></html>"""

# ==============================================================================
#  MAIN UI HTML
# ==============================================================================
HTML = r"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>RailVPS Pro — Control Panel</title>
<link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/xterm@5.3.0/css/xterm.min.css">
<script src="https://cdn.jsdelivr.net/npm/xterm@5.3.0/lib/xterm.min.js"></script>
<script src="https://cdn.jsdelivr.net/npm/xterm-addon-fit@0.8.0/lib/xterm-addon-fit.min.js"></script>
<style>
:root{
  --bg:#080b10;--panel:#0f1520;--panel2:#0b1119;--border:#1c2531;
  --text:#d7e0ea;--muted:#6d7c8e;--dim:#4a5768;
  --accent:#3ea6ff;--green:#2ecc71;--red:#ff5c5c;--amber:#f5a623;--purple:#a67cff;
}
*{box-sizing:border-box;margin:0;padding:0}
html,body{height:100%}
body{background:var(--bg);color:var(--text);font-size:13px;
  font-family:ui-monospace,SFMono-Regular,Menlo,Consolas,"Liberation Mono",monospace;
  display:flex;flex-direction:column;overflow:hidden}
::-webkit-scrollbar{width:10px;height:10px}
::-webkit-scrollbar-track{background:#0a0f17}
::-webkit-scrollbar-thumb{background:#1e2733;border-radius:6px}
::-webkit-scrollbar-thumb:hover{background:#2c3a4d}
.topbar{height:46px;flex:0 0 46px;display:flex;align-items:center;gap:16px;
  padding:0 16px;background:var(--panel);border-bottom:1px solid var(--border)}
.brand{display:flex;align-items:center;gap:9px;font-weight:700;letter-spacing:.6px}
.brand .dot{width:8px;height:8px;border-radius:50%;background:var(--green);
  box-shadow:0 0 10px var(--green);animation:pulse 2.4s infinite}
@keyframes pulse{50%{opacity:.35}}
.brand .v{color:var(--dim);font-weight:400;font-size:10.5px}
.topinfo{display:flex;gap:18px;color:var(--muted);font-size:11.5px;margin-left:auto;flex-wrap:wrap}
.topinfo b{color:var(--text);font-weight:600}
.ephemeral{background:#3a1f0a;border:1px solid #7a4410;color:#ffb84d;
  padding:2px 8px;border-radius:5px;font-size:10.5px}
.logout{color:var(--red);text-decoration:none;border:1px solid #3a1f1f;background:#1a0f0f;
  padding:5px 11px;border-radius:6px;font-size:11.5px}
.logout:hover{background:#241313}
.shell{flex:1;display:flex;min-height:0}
.sidebar{width:200px;flex:0 0 200px;background:var(--panel2);border-right:1px solid var(--border);
  padding:12px 9px;display:flex;flex-direction:column;gap:3px;overflow-y:auto}
.nav{display:flex;align-items:center;gap:10px;padding:8px 11px;border-radius:7px;
  color:var(--muted);cursor:pointer;font-size:12.5px;user-select:none;border:1px solid transparent;transition:.12s}
.nav:hover{background:#101823;color:var(--text)}
.nav.active{background:#132133;color:var(--accent);border-color:#1d3350}
.nav .ic{width:16px;text-align:center;font-size:13px}
.sidefoot{margin-top:auto;padding:10px 11px;color:var(--dim);font-size:10px;line-height:1.7;
  border-top:1px solid var(--border);word-break:break-all}
.main{flex:1;min-width:0;overflow-y:auto;padding:18px 20px 40px}
.view{display:none}.view.active{display:block}
h2.title{font-size:15px;margin-bottom:3px;letter-spacing:.4px}
p.desc{color:var(--muted);font-size:11.5px;margin-bottom:16px}
.card{background:var(--panel);border:1px solid var(--border);border-radius:10px;padding:15px 16px}
.grid{display:grid;gap:13px}
.g4{grid-template-columns:repeat(auto-fit,minmax(210px,1fr))}
.g2{grid-template-columns:repeat(auto-fit,minmax(320px,1fr))}
.row{display:flex;align-items:center;gap:9px;flex-wrap:wrap}
.spacer{flex:1}
.btn{background:#141d29;border:1px solid var(--border);color:var(--text);
  padding:7px 13px;border-radius:7px;cursor:pointer;font-family:inherit;font-size:12px;
  transition:.12s;white-space:nowrap}
.btn:hover{background:#1b2634;border-color:#2c3a4d}
.btn.primary{background:linear-gradient(180deg,#3ea6ff,#1f7fe0);border-color:#1f7fe0;color:#fff;font-weight:600}
.btn.primary:hover{filter:brightness(1.12)}
.btn.danger{color:var(--red);border-color:#3a1f1f;background:#170d0d}
.btn.danger:hover{background:#221111}
.btn.sm{padding:4px 9px;font-size:11px}
.btn:disabled{opacity:.45;cursor:not-allowed}
input[type=text],input[type=password],input[type=number],select,textarea{
  background:#0a0f17;border:1px solid var(--border);border-radius:7px;color:var(--text);
  padding:8px 11px;font-family:inherit;font-size:12.5px;outline:none;transition:.15s}
input:focus,select:focus,textarea:focus{border-color:var(--accent);box-shadow:0 0 0 3px rgba(62,166,255,.12)}
label.f{display:block;font-size:10.5px;color:var(--muted);text-transform:uppercase;
  letter-spacing:1px;margin-bottom:5px}
.stat{background:var(--panel);border:1px solid var(--border);border-radius:10px;padding:14px 15px}
.stat .lbl{color:var(--muted);font-size:10.5px;text-transform:uppercase;letter-spacing:1.1px;
  margin-bottom:9px;display:flex;justify-content:space-between}
.stat .val{font-size:22px;font-weight:700;letter-spacing:-.5px}
.stat .sub{color:var(--dim);font-size:11px;margin-top:5px}
.bar{height:6px;background:#0a0f17;border-radius:4px;overflow:hidden;margin-top:11px}
.bar > i{display:block;height:100%;border-radius:4px;transition:width .5s ease}
.b-blue{background:linear-gradient(90deg,#1f7fe0,#3ea6ff)}
.b-green{background:linear-gradient(90deg,#1e9e57,#2ecc71)}
.b-amber{background:linear-gradient(90deg,#c47f10,#f5a623)}
.b-red{background:linear-gradient(90deg,#c23b3b,#ff5c5c)}
table{width:100%;border-collapse:collapse;font-size:12px}
th{text-align:left;color:var(--muted);font-weight:500;font-size:10.5px;
  text-transform:uppercase;letter-spacing:.9px;padding:8px 10px;border-bottom:1px solid var(--border)}
td{padding:7px 10px;border-bottom:1px solid #131b25;vertical-align:top}
tr:hover td{background:#0e1621}
.pill{display:inline-block;padding:1px 8px;border-radius:20px;font-size:10px;border:1px solid}
.pill.g{color:var(--green);border-color:#1d4a2f;background:#0d1d14}
.pill.r{color:var(--red);border-color:#4a1d1d;background:#1d0d0d}
.pill.b{color:var(--accent);border-color:#1d3350;background:#0d1724}
.pill.a{color:var(--amber);border-color:#4a3715;background:#1e1508}
.muted{color:var(--muted)}.dim{color:var(--dim)}
.empty{padding:40px;text-align:center;color:var(--dim);font-size:12px}
.crumbs{display:flex;align-items:center;gap:5px;flex-wrap:wrap;font-size:12.5px;margin-bottom:12px}
.crumbs a{color:var(--accent);text-decoration:none;cursor:pointer}
.crumbs a:hover{text-decoration:underline}
.crumbs .sep{color:var(--dim)}
.frow{cursor:pointer}
.frow .nm{display:flex;align-items:center;gap:8px}
.ficon{width:16px;text-align:center;opacity:.9}
.acts{display:flex;gap:5px;justify-content:flex-end;opacity:0;transition:.12s}
tr:hover .acts{opacity:1}
#drop{border:2px dashed #22303f;border-radius:10px;padding:22px;text-align:center;
  color:var(--muted);font-size:12px;margin-bottom:13px;transition:.15s}
#drop.over{border-color:var(--accent);background:#0d1724;color:var(--accent)}
.termline{display:flex;gap:0;align-items:stretch;margin-top:0;background:#05080c;
  border:1px solid var(--border);border-top:0;border-radius:0 0 10px 10px;padding:6px 10px}
.termline input{flex:1;background:transparent;border:0;padding:4px 6px;outline:none;
  font-family:inherit;font-size:12.5px;color:#cfe0f0}
#editor{width:100%;height:calc(100vh - 260px);min-height:320px;resize:vertical;
  background:#05080c;border:1px solid var(--border);border-radius:10px;
  padding:14px;font-size:12.5px;line-height:1.6;color:#cfe0f0;white-space:pre;
  overflow:auto;tab-size:4;font-family:inherit}
#toasts{position:fixed;right:18px;bottom:18px;display:flex;flex-direction:column;gap:8px;z-index:999}
.toast{background:#111a25;border:1px solid var(--border);border-left:3px solid var(--accent);
  padding:10px 15px;border-radius:7px;font-size:12px;min-width:220px;
  box-shadow:0 10px 30px rgba(0,0,0,.6);animation:slide .22s ease}
.toast.ok{border-left-color:var(--green)}
.toast.err{border-left-color:var(--red)}
@keyframes slide{from{transform:translateX(30px);opacity:0}}
.modal{position:fixed;inset:0;background:rgba(3,6,10,.82);display:none;
  align-items:center;justify-content:center;z-index:1000;padding:20px}
.modal.show{display:flex}
.modal .box{background:var(--panel);border:1px solid var(--border);border-radius:12px;
  padding:20px;width:min(440px,94vw);box-shadow:0 24px 70px rgba(0,0,0,.8)}
.modal h3{font-size:14px;margin-bottom:15px}
.modal .field{margin-bottom:13px}
.modal .actions{display:flex;gap:9px;justify-content:flex-end;margin-top:18px}
@media(max-width:760px){
  .sidebar{width:56px;flex:0 0 56px}
  .nav span.t{display:none}
  .sidefoot{display:none}
  .topinfo{display:none}
}
.kv{display:grid;grid-template-columns:180px 1fr;gap:0;font-size:12px}
.kv > div{padding:5px 8px;border-bottom:1px solid #131b25;word-break:break-all}
.kv > div:nth-child(odd){color:var(--muted)}
.grid-mini{display:grid;grid-template-columns:repeat(auto-fill,minmax(60px,1fr));gap:5px;margin-top:8px}
.grid-mini > div{background:#0a0f17;border-radius:5px;padding:5px;font-size:10px;text-align:center}
.grid-mini > div > .b{height:4px;background:#1a2530;border-radius:2px;margin-top:3px;overflow:hidden}
.grid-mini > div > .b > i{display:block;height:100%;background:var(--accent)}
.log-view{background:#05080c;border:1px solid var(--border);border-radius:10px;
  padding:12px;font-size:12px;line-height:1.5;white-space:pre-wrap;max-height:60vh;
  overflow:auto;color:#cfe0f0}
.banner-warn{background:#3a1f0a;border:1px solid #7a4410;color:#ffb84d;
  padding:10px 14px;border-radius:8px;font-size:12px;margin-bottom:14px}
</style>
</head>
<body>

<div class="topbar">
  <div class="brand"><span class="dot"></span>RailVPS Pro <span class="v" id="ver">v2.0.0</span></div>
  <div class="topinfo">
    <div id="tb-env-wrap"></div>
    <div>host <b id="tb-host">—</b></div>
    <div>os <b id="tb-os">—</b></div>
    <div>uptime <b id="tb-up">—</b></div>
    <div>load <b id="tb-load">—</b></div>
  </div>
  <a class="logout" href="/logout">logout</a>
</div>

<div class="shell">
  <aside class="sidebar">
    <div class="nav active" data-view="dash"><span class="ic">▤</span><span class="t">Dashboard</span></div>
    <div class="nav" data-view="files"><span class="ic">▣</span><span class="t">Files</span></div>
    <div class="nav" data-view="term"><span class="ic">▸</span><span class="t">Terminal</span></div>
    <div class="nav" data-view="proc"><span class="ic">⚙</span><span class="t">Processes</span></div>
    <div class="nav" data-view="sites"><span class="ic">◈</span><span class="t">Sites</span></div>
    <div class="nav" data-view="cron"><span class="ic">⏱</span><span class="t">Scheduler</span></div>
    <div class="nav" data-view="net"><span class="ic">◎</span><span class="t">Network</span></div>
    <div class="nav" data-view="pip"><span class="ic">⬢</span><span class="t">Packages</span></div>
    <div class="nav" data-view="backup"><span class="ic">⛁</span><span class="t">Backups</span></div>
    <div class="nav" data-view="logs"><span class="ic">☰</span><span class="t">Logs</span></div>
    <div class="nav" data-view="env"><span class="ic">≡</span><span class="t">Env</span></div>
    <div class="nav" data-view="users"><span class="ic">☻</span><span class="t">Users</span></div>
    <div class="nav" data-view="sys"><span class="ic">ℹ</span><span class="t">System</span></div>
    <div class="sidefoot">
      <div>root <span class="dim" id="sf-root">/var/data/files</span></div>
      <div id="sf-store" class="dim">storage —</div>
    </div>
  </aside>

  <main class="main" id="main">

    <section class="view active" id="v-dash">
      <h2 class="title">System Overview</h2>
      <p class="desc">Live resource utilisation of this container.</p>
      <div id="ephemeral-banner"></div>
      <div class="grid g4">
        <div class="stat">
          <div class="lbl"><span>CPU</span><span id="s-cpu-n" class="dim">—</span></div>
          <div class="val" id="s-cpu">0%</div>
          <div class="bar"><i id="b-cpu" class="b-blue" style="width:0"></i></div>
          <div class="sub" id="s-cpu-sub">load —</div>
          <div class="grid-mini" id="cpu-cores"></div>
        </div>
        <div class="stat">
          <div class="lbl"><span>Memory</span><span id="s-mem-h" class="dim">—</span></div>
          <div class="val" id="s-mem">0%</div>
          <div class="bar"><i id="b-mem" class="b-green" style="width:0"></i></div>
          <div class="sub" id="s-mem-sub">—</div>
          <div class="sub" id="s-swap" style="margin-top:6px"></div>
        </div>
        <div class="stat">
          <div class="lbl"><span>Disk</span><span id="s-dsk-h" class="dim">—</span></div>
          <div class="val" id="s-dsk">0%</div>
          <div class="bar"><i id="b-dsk" class="b-amber" style="width:0"></i></div>
          <div class="sub" id="s-dsk-sub">—</div>
        </div>
        <div class="stat">
          <div class="lbl"><span>Network</span><span class="dim">rx/tx</span></div>
          <div class="val" id="s-net" style="font-size:15px">—</div>
          <div class="sub" id="s-net-sub">—</div>
        </div>
      </div>
      <div class="grid g2" style="margin-top:15px">
        <div class="card">
          <h2 class="title" style="font-size:13px;margin-bottom:12px">System Information</h2>
          <div id="sysinfo" class="kv"></div>
        </div>
        <div class="card">
          <h2 class="title" style="font-size:13px;margin-bottom:12px">Top Processes</h2>
          <table><thead><tr><th>PID</th><th>Name</th>
            <th style="text-align:right">CPU%</th><th style="text-align:right">MEM%</th>
          </tr></thead><tbody id="dash-procs"></tbody></table>
        </div>
      </div>
    </section>

    <section class="view" id="v-files">
      <h2 class="title">File Manager</h2>
      <p class="desc">Root: <span id="files-root">/var/data/files</span></p>
      <div id="drop">Drop files here · or
        <label class="btn sm" style="display:inline-block;cursor:pointer">browse
          <input type="file" id="up-input" multiple hidden></label>
        <label class="btn sm" style="display:inline-block;cursor:pointer">folder
          <input type="file" id="up-dir" webkitdirectory directory multiple hidden></label>
      </div>
      <div class="row" style="margin-bottom:12px">
        <button class="btn sm" id="btn-newfile">+ File</button>
        <button class="btn sm" id="btn-newdir">+ Folder</button>
        <button class="btn sm" id="btn-refresh">⟳</button>
        <button class="btn sm" id="btn-zip">⤓ ZIP</button>
        <button class="btn sm" id="btn-search-toggle">🔍 Search</button>
        <div class="spacer"></div>
        <span class="muted" id="files-count" style="font-size:11.5px"></span>
      </div>
      <div class="card" id="search-card" style="margin-bottom:12px;display:none">
        <div class="row">
          <input type="text" id="sq" placeholder="search query…" style="flex:1;min-width:200px">
          <select id="smode">
            <option value="name">by name</option>
            <option value="content">by content</option>
            <option value="regex">by regex</option>
          </select>
          <button class="btn primary sm" id="btn-search">Search</button>
        </div>
        <div id="search-results" style="margin-top:10px"></div>
      </div>
      <div class="crumbs" id="crumbs"></div>
      <div class="card" style="padding:0;overflow:hidden">
        <table><thead><tr>
          <th style="width:44%">Name</th>
          <th style="width:10%">Size</th>
          <th style="width:8%">Mode</th>
          <th style="width:20%">Modified</th>
          <th style="text-align:right">Actions</th>
        </tr></thead><tbody id="files-body"></tbody></table>
      </div>
    </section>

    <section class="view" id="v-term">
      <h2 class="title">Web Terminal</h2>
      <p class="desc">Real PTY bash. Full interactive shell. Click the terminal to focus.</p>
      <div id="term-wrap" style="background:#05080c;border:1px solid var(--border);
           border-radius:10px;padding:8px 4px 4px 8px;
           height:calc(100vh - 230px);min-height:320px;overflow:hidden">
        <div id="term" style="width:100%;height:100%"></div>
      </div>
      <div class="termline" style="margin-top:8px;border-radius:10px;border-top:1px solid var(--border);justify-content:flex-start;gap:9px">
        <button class="btn sm" id="btn-kill-shell" title="Kill shell">✕ kill shell</button>
        <button class="btn sm" id="btn-clear">clear</button>
        <span class="muted" id="term-status" style="margin-left:auto;font-size:11px"></span>
      </div>
    </section>

    <section class="view" id="v-proc">
      <h2 class="title">Process Manager</h2>
      <p class="desc">Live processes · send signals · view tree.</p>
      <div class="row" style="margin-bottom:12px">
        <button class="btn sm" id="btn-proc-refresh">⟳ Refresh</button>
        <button class="btn sm" id="btn-proc-tree">Tree</button>
      </div>
      <div class="card" style="padding:0;overflow:hidden">
        <table><thead><tr>
          <th>PID</th><th>Name</th><th>User</th><th>Status</th>
          <th style="text-align:right">CPU%</th><th style="text-align:right">MEM%</th>
          <th style="text-align:right">Signals</th>
        </tr></thead><tbody id="proc-body"></tbody></table>
      </div>
      <div id="tree-view" style="display:none;margin-top:14px" class="card">
        <h2 class="title" style="font-size:13px;margin-bottom:10px">Process Tree</h2>
        <div id="tree-content" style="font-family:inherit;font-size:12px;line-height:1.7"></div>
      </div>
    </section>

    <section class="view" id="v-sites">
      <h2 class="title">Site Hosting</h2>
      <p class="desc">Map folders to public endpoints at <code>/s/&lt;name&gt;/</code></p>
      <div class="card" style="margin-bottom:15px">
        <div class="row">
          <div><label class="f">Name</label>
            <input type="text" id="st-name" placeholder="myapp" style="width:150px"></div>
          <div><label class="f">Folder</label>
            <input type="text" id="st-dir" placeholder="myapp" style="width:180px"></div>
          <div><label class="f">Index</label>
            <input type="text" id="st-index" value="index.html" style="width:130px"></div>
          <div><label class="f">SPA</label>
            <select id="st-spa"><option value="0">No</option><option value="1">Yes</option></select></div>
          <div style="padding-top:18px">
            <button class="btn primary" id="btn-site-add">Create</button></div>
        </div>
      </div>
      <div class="card" style="padding:0;overflow:hidden">
        <table><thead><tr>
          <th>Site</th><th>Folder</th><th>URL</th><th>Size</th>
          <th style="text-align:right">Actions</th>
        </tr></thead><tbody id="sites-body"></tbody></table>
      </div>
    </section>

    <section class="view" id="v-cron">
      <h2 class="title">Task Scheduler</h2>
      <p class="desc">Run commands on an interval (min 10 s). Output captured.</p>
      <div class="card" style="margin-bottom:15px">
        <div class="row">
          <div><label class="f">Name</label>
            <input type="text" id="cj-name" placeholder="cleanup" style="width:160px"></div>
          <div style="flex:1;min-width:220px"><label class="f">Command</label>
            <input type="text" id="cj-cmd" placeholder="echo hello >> /var/data/files/log.txt" style="width:100%"></div>
          <div><label class="f">Interval (s)</label>
            <input type="number" id="cj-int" value="300" min="10" style="width:110px"></div>
          <div style="padding-top:18px"><button class="btn primary" id="btn-cron-add">Add</button></div>
        </div>
      </div>
      <div class="card" style="padding:0;overflow:hidden">
        <table><thead><tr>
          <th>Name</th><th>Command</th><th>Interval</th><th>Last run</th>
          <th>Last code</th><th style="text-align:right">Actions</th>
        </tr></thead><tbody id="cron-body"></tbody></table>
      </div>
      <div id="cron-output-card" class="card" style="display:none;margin-top:14px">
        <h2 class="title" style="font-size:13px;margin-bottom:10px">
          Output: <span id="cron-output-name"></span>
          <button class="btn sm" style="float:right" id="btn-cron-output-close">close</button>
        </h2>
        <div id="cron-output" class="log-view" style="max-height:40vh"></div>
      </div>
    </section>

    <section class="view" id="v-net">
      <h2 class="title">Network Tools</h2>
      <p class="desc">Ping, DNS, HTTP fetch, public IP, ports, interfaces.</p>
      <div class="grid g2">
        <div class="card">
          <h2 class="title" style="font-size:13px;margin-bottom:12px">Ping</h2>
          <div class="row">
            <input type="text" id="pg-host" placeholder="1.1.1.1" style="flex:1">
            <button class="btn primary" id="btn-ping">Ping</button>
          </div>
          <pre id="pg-out" class="log-view" style="margin-top:10px;display:none"></pre>
        </div>
        <div class="card">
          <h2 class="title" style="font-size:13px;margin-bottom:12px">DNS Lookup</h2>
          <div class="row">
            <input type="text" id="dns-host" placeholder="example.com" style="flex:1">
            <button class="btn primary" id="btn-dns">Resolve</button>
          </div>
          <div id="dns-out" style="margin-top:10px;font-size:12px"></div>
        </div>
        <div class="card">
          <h2 class="title" style="font-size:13px;margin-bottom:12px">HTTP Fetch</h2>
          <div class="row">
            <select id="curl-m"><option>GET</option><option>HEAD</option></select>
            <input type="text" id="curl-url" placeholder="https://api.ipify.org" style="flex:1">
            <button class="btn primary" id="btn-curl">Fetch</button>
          </div>
          <pre id="curl-out" class="log-view" style="margin-top:10px;display:none"></pre>
        </div>
        <div class="card">
          <h2 class="title" style="font-size:13px;margin-bottom:12px">Public IP</h2>
          <button class="btn primary" id="btn-pubip">Detect</button>
          <div id="pubip-out" style="margin-top:10px;font-size:13px"></div>
        </div>
      </div>
      <div class="grid g2" style="margin-top:14px">
        <div class="card">
          <h2 class="title" style="font-size:13px;margin-bottom:12px">Listening Ports</h2>
          <div class="row" style="margin-bottom:8px"><button class="btn sm" id="btn-ports">⟳</button></div>
          <table><thead><tr><th>Port</th><th>Addr</th><th>PID</th><th>Process</th></tr></thead>
          <tbody id="ports-body"></tbody></table>
        </div>
        <div class="card">
          <h2 class="title" style="font-size:13px;margin-bottom:12px">Interfaces</h2>
          <div class="row" style="margin-bottom:8px"><button class="btn sm" id="btn-ifaces">⟳</button></div>
          <div id="ifaces-out" style="font-size:12px"></div>
        </div>
      </div>
    </section>

    <section class="view" id="v-pip">
      <h2 class="title">Python Packages</h2>
      <p class="desc">Manage pip packages in the running environment.</p>
      <div class="card" style="margin-bottom:12px">
        <div class="row">
          <input type="text" id="pip-pkg" placeholder="package name(s) comma-separated" style="flex:1;min-width:220px">
          <button class="btn primary" id="btn-pip-install">Install</button>
          <button class="btn danger" id="btn-pip-uninstall">Uninstall</button>
          <button class="btn sm" id="btn-pip-refresh">⟳</button>
        </div>
        <input type="text" id="pip-filter" placeholder="filter…" style="width:100%;margin-top:9px">
      </div>
      <div class="card" style="padding:0;overflow:hidden;max-height:60vh;overflow-y:auto">
        <table><thead><tr><th>Package</th><th>Version</th></tr></thead>
        <tbody id="pip-body"></tbody></table>
      </div>
      <pre id="pip-log" class="log-view" style="margin-top:12px;display:none"></pre>
    </section>

    <section class="view" id="v-backup">
      <h2 class="title">Backups</h2>
      <p class="desc">Full snapshots of file root + configuration.</p>
      <div class="row" style="margin-bottom:12px">
        <button class="btn primary" id="btn-backup-create">Create backup</button>
        <button class="btn sm" id="btn-backup-refresh">⟳</button>
      </div>
      <div class="card" style="padding:0;overflow:hidden">
        <table><thead><tr>
          <th>Name</th><th>Size</th><th>Created</th>
          <th style="text-align:right">Actions</th>
        </tr></thead><tbody id="backup-body"></tbody></table>
      </div>
    </section>

    <section class="view" id="v-logs">
      <h2 class="title">Log Viewer</h2>
      <p class="desc">Tail log files from the container.</p>
      <div class="grid g2">
        <div class="card" style="padding:0;overflow:hidden">
          <table><thead><tr><th>Log</th><th style="text-align:right">Size</th></tr></thead>
          <tbody id="logs-body"></tbody></table>
        </div>
        <div class="card">
          <div class="row" style="margin-bottom:9px">
            <b id="log-title" class="muted" style="font-size:12px">select a log</b>
            <span class="spacer"></span>
            <button class="btn sm" id="btn-log-refresh">⟳</button>
          </div>
          <pre id="log-content" class="log-view" style="max-height:55vh">—</pre>
        </div>
      </div>
    </section>

    <section class="view" id="v-env">
      <h2 class="title">Environment Variables</h2>
      <p class="desc">Custom vars stored in config (not injected into process).</p>
      <div class="card" style="margin-bottom:12px">
        <div class="row">
          <input type="text" id="env-key" placeholder="KEY" style="width:220px">
          <input type="text" id="env-val" placeholder="value" style="flex:1;min-width:180px">
          <button class="btn primary" id="btn-env-set">Set</button>
        </div>
      </div>
      <div class="grid g2">
        <div class="card">
          <h2 class="title" style="font-size:13px;margin-bottom:10px">Custom</h2>
          <table><thead><tr><th>Key</th><th>Value</th><th></th></tr></thead>
          <tbody id="env-custom"></tbody></table>
        </div>
        <div class="card" style="max-height:60vh;overflow-y:auto">
          <h2 class="title" style="font-size:13px;margin-bottom:10px">System (read-only)</h2>
          <table><thead><tr><th>Key</th><th>Value</th></tr></thead>
          <tbody id="env-system"></tbody></table>
        </div>
      </div>
    </section>

    <section class="view" id="v-users">
      <h2 class="title">Users</h2>
      <p class="desc">App-level users. Admin role can manage others.</p>
      <div class="card" style="margin-bottom:12px">
        <div class="row">
          <input type="text" id="usr-name" placeholder="username" style="width:170px">
          <input type="password" id="usr-pass" placeholder="password" style="width:170px">
          <select id="usr-role"><option value="user">user</option><option value="admin">admin</option></select>
          <button class="btn primary" id="btn-usr-add">Add</button>
          <span class="spacer"></span>
          <input type="password" id="pw-old" placeholder="current" style="width:130px">
          <input type="password" id="pw-new" placeholder="new" style="width:130px">
          <button class="btn sm" id="btn-pw">Change my password</button>
        </div>
      </div>
      <div class="card" style="padding:0;overflow:hidden">
        <table><thead><tr><th>User</th><th>Role</th><th>Created</th><th></th></tr></thead>
        <tbody id="users-body"></tbody></table>
      </div>
    </section>

    <section class="view" id="v-sys">
      <h2 class="title">System Information</h2>
      <div class="row" style="margin-bottom:12px">
        <button class="btn sm" id="btn-sys-refresh">⟳ Refresh</button>
      </div>
      <div class="card"><div id="sysinfo-full" class="kv"></div></div>
    </section>

  </main>
</div>

<div id="toasts"></div>

<div class="modal" id="modal">
  <div class="box">
    <h3 id="m-title">Input</h3>
    <div class="field">
      <label class="f" id="m-label">Value</label>
      <input type="text" id="m-input" style="width:100%">
    </div>
    <div class="actions">
      <button class="btn" id="m-cancel">Cancel</button>
      <button class="btn primary" id="m-ok">Confirm</button>
    </div>
  </div>
</div>

<script>
const $ = (s,r=document)=>r.querySelector(s);
const $$ = (s,r=document)=>Array.from(r.querySelectorAll(s));

function toast(msg,kind=''){const el=document.createElement('div');
  el.className='toast '+kind;el.textContent=msg;$('#toasts').appendChild(el);
  setTimeout(()=>{el.style.opacity='0';el.style.transition='.3s';},2400);
  setTimeout(()=>el.remove(),2800);}
function esc(s){return String(s==null?'':s)
  .replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;')
  .replace(/"/g,'&quot;').replace(/'/g,'&#39;');}
function fmtBytes(b){if(!b&&b!==0)return '0 B';const u=['B','KB','MB','GB','TB','PB'];
  let i=0;while(b>=1024&&i<u.length-1){b/=1024;i++;}return (i?b.toFixed(1):Math.round(b))+' '+u[i];}
function fmtUptime(sec){sec=Math.floor(sec||0);const d=Math.floor(sec/86400),
  h=Math.floor(sec%86400/3600),m=Math.floor(sec%3600/60);
  return (d?d+'d ':'')+h+'h '+m+'m';}
async function api(path,opts={}){const r=await fetch(path,{credentials:'same-origin',...opts});
  if(r.status===401){location.href='/login';throw new Error('unauthorized');}return r;}
async function apiJSON(path,opts={}){return (await api(path,opts)).json();}
function postJSON(path,body){return apiJSON(path,{method:'POST',
  headers:{'Content-Type':'application/json'},body:JSON.stringify(body||{})});}
function prompt2(title,label,value=''){return new Promise(resolve=>{
  const m=$('#modal');$('#m-title').textContent=title;$('#m-label').textContent=label;
  const inp=$('#m-input');inp.value=value;m.classList.add('show');
  setTimeout(()=>inp.focus(),40);
  const done=v=>{m.classList.remove('show');$('#m-ok').onclick=null;
    $('#m-cancel').onclick=null;inp.onkeydown=null;resolve(v);};
  $('#m-ok').onclick=()=>done(inp.value.trim());
  $('#m-cancel').onclick=()=>done(null);
  inp.onkeydown=e=>{if(e.key==='Enter')done(inp.value.trim());
                    if(e.key==='Escape')done(null);};});}

let currentView='dash';
$$('.nav').forEach(n=>n.addEventListener('click',()=>{
  $$('.nav').forEach(x=>x.classList.remove('active'));
  n.classList.add('active');
  $$('.view').forEach(v=>v.classList.remove('active'));
  currentView=n.dataset.view;
  $('#v-'+currentView).classList.add('active');
  if(currentView==='files')loadFiles(cwd);
  if(currentView==='sites')loadSites();
  if(currentView==='proc')loadProcs();
  if(currentView==='dash')loadStats();
  if(currentView==='cron')loadCron();
  if(currentView==='backup')loadBackups();
  if(currentView==='logs')loadLogs();
  if(currentView==='env')loadEnv();
  if(currentView==='users')loadUsers();
  if(currentView==='sys')loadSysFull();
  if(currentView==='pip')loadPip();
  if(currentView==='net'){loadPorts();loadIfaces();}
  if(currentView==='term')setTimeout(()=>{ensureTerm();if(xterm){try{fitAddon.fit();}catch(e){}xterm.focus();}},60);
}));

async function loadStats(){
  try{
    const d=await apiJSON('/api/stats');
    $('#ver').textContent='v'+(d.version||'2.0.0');
    $('#tb-host').textContent=d.hostname||'—';
    $('#tb-os').textContent=(d.platform||'—').slice(0,26);
    $('#tb-up').textContent=fmtUptime(d.uptime);
    $('#sf-root').textContent=d.data_dir||'/var/data';
    if(d.storage)$('#sf-store').textContent=d.storage.human+' · '+d.storage.files+' files';
    if(d.on_render){
      $('#tb-env-wrap').innerHTML='<span class="ephemeral">Render</span>';
    }
    if(d.ephemeral){
      $('#ephemeral-banner').innerHTML='<div class="banner-warn">'+
        '<b>⚠ Ephemeral storage.</b> Data is stored at <code>'+esc(d.data_dir)+
        '</code> which does NOT persist across redeploys on Render. '+
        'Add a <b>Disk</b> mounted at <code>/var/data</code> and set '+
        '<code>DATA_DIR=/var/data</code> to persist.</div>';
    } else { $('#ephemeral-banner').innerHTML=''; }

    if(d.cpu){const c=Math.round(d.cpu.percent);
      $('#s-cpu').textContent=c+'%';$('#b-cpu').style.width=c+'%';
      $('#s-cpu-n').textContent=d.cpu.cores+' cores';
      const ld=(d.cpu.load||[0,0,0]).map(x=>(+x).toFixed(2)).join(' / ');
      $('#s-cpu-sub').textContent='load '+ld;$('#tb-load').textContent=ld;
      const pc=d.cpu.per_core||[];
      $('#cpu-cores').innerHTML=pc.map((v,i)=>
        `<div>c${i}<div class="b"><i style="width:${v}%"></i></div></div>`).join('');}
    if(d.memory){const m=d.memory;
      $('#s-mem').textContent=Math.round(m.percent)+'%';
      $('#b-mem').style.width=m.percent+'%';
      $('#s-mem-h').textContent=m.total_h;
      $('#s-mem-sub').textContent=m.used_h+' used · '+m.free_h+' free';}
    if(d.swap&&d.swap.total){$('#s-swap').textContent=
      'swap '+d.swap.used_h+' / '+d.swap.total_h;}
    if(d.disk){const k=d.disk;
      $('#s-dsk').textContent=Math.round(k.percent)+'%';
      $('#b-dsk').style.width=k.percent+'%';
      $('#b-dsk').className='b-'+(k.percent>85?'red':k.percent>65?'amber':'green');
      $('#s-dsk-h').textContent=k.total_h;
      $('#s-dsk-sub').textContent=k.used_h+' used · '+k.free_h+' free';}
    if(d.network){$('#s-net').textContent=d.network.recv_h+' ↓';
      $('#s-net-sub').textContent=d.network.sent_h+' ↑ · '+
        (d.network.packets_recv+d.network.packets_sent).toLocaleString()+' pkt';}
    const rows=[
      ['Hostname',d.hostname],['Platform',d.platform],['Architecture',d.arch],
      ['Python',d.python],['Processes',d.processes],
      ['Boot time',d.boot_time?new Date(d.boot_time*1000).toLocaleString():'—'],
      ['Data dir',d.data_dir+' '+(d.ephemeral?'(ephemeral)':'(persistent)')],
      ['App',d.app+' '+d.version],
      ['Server time',new Date(d.time_epoch*1000).toLocaleString()],
    ];
    $('#sysinfo').innerHTML=rows.map(r=>
      `<div>${esc(r[0])}</div><div>${esc(r[1])}</div>`).join('');
  }catch(e){}
}
async function loadDashProcs(){
  try{const d=await apiJSON('/api/processes');
    $('#dash-procs').innerHTML=(d.processes||[]).slice(0,10).map(p=>
      `<tr><td class="dim">${p.pid}</td><td>${esc(p.name)}</td>
       <td style="text-align:right" class="muted">${p.cpu}</td>
       <td style="text-align:right" class="muted">${p.mem}</td></tr>`
    ).join('')||'<tr><td colspan="4" class="empty">no data</td></tr>';
  }catch(e){}
}

let cwd='/';
const ICONS={dir:'📁',html:'🌐',htm:'🌐',css:'🎨',js:'📜',mjs:'📜',json:'⚙',
  py:'🐍',txt:'📄',md:'📝',png:'🖼',jpg:'🖼',jpeg:'🖼',gif:'🖼',svg:'🖼',webp:'🖼',
  ico:'🖼',zip:'📦',tar:'📦',gz:'📦',mp4:'🎬',mp3:'🎵',pdf:'📕',sh:'⚡',yml:'⚙',
  yaml:'⚙',toml:'⚙',env:'🔑',sql:'🗄',csv:'📊',log:'📃',so:'⚙'};
const iconFor=e=>e.dir?ICONS.dir:(ICONS[e.ext]||'📄');

async function loadFiles(path){
  cwd=path||cwd;
  try{
    const d=await apiJSON('/api/files?path='+encodeURIComponent(cwd));
    if(!d.ok){toast(d.error||'Error','err');return;}
    cwd=d.path;renderCrumbs(cwd);
    $('#files-count').textContent=d.count+' items';
    $('#files-root').textContent=(await apiJSON('/api/stats')).data_dir+'/files';
    const body=$('#files-body');
    if(!d.entries.length){body.innerHTML='<tr><td colspan="5" class="empty">empty directory</td></tr>';return;}
    body.innerHTML=d.entries.map(e=>`
      <tr class="frow" data-path="${esc(e.path)}" data-dir="${e.dir}" data-text="${e.text}">
        <td><div class="nm"><span class="ficon">${iconFor(e)}</span>
          <span>${esc(e.name)}</span>${e.symlink?' <span class="pill a">link</span>':''}</div></td>
        <td class="muted">${e.dir?'—':esc(e.size_h)}</td>
        <td class="dim">${esc(e.mode)}</td>
        <td class="dim">${esc(e.mtime_h)}</td>
        <td><div class="acts">
          ${e.dir?'':`<button class="btn sm" data-act="edit">✎</button>`}
          ${e.dir?'':`<button class="btn sm" data-act="dl">⤓</button>`}
          ${e.dir?'':`<button class="btn sm" data-act="extract">✂</button>`}
          <button class="btn sm" data-act="zip">📦</button>
          <button class="btn sm" data-act="copy">⎘</button>
          <button class="btn sm" data-act="chmod">#</button>
          <button class="btn sm" data-act="ren">↻</button>
          <button class="btn sm danger" data-act="del">✕</button>
        </div></td>
      </tr>`).join('');
    $$('#files-body .frow').forEach(row=>{
      row.addEventListener('click',ev=>{
        if(ev.target.closest('button'))return;
        const p=row.dataset.path;
        if(row.dataset.dir==='true')loadFiles(p);else openEditor(p);});
    });
    $$('#files-body button').forEach(b=>b.addEventListener('click',async ev=>{
      ev.stopPropagation();
      const row=b.closest('.frow');const p=row.dataset.path;const act=b.dataset.act;
      if(act==='edit')openEditor(p);
      else if(act==='dl')location.href='/api/file/download?path='+encodeURIComponent(p);
      else if(act==='zip')location.href='/api/file/zip?path='+encodeURIComponent(p);
      else if(act==='extract'){const r=await postJSON('/api/file/extract',{path:p});
        toast(r.ok?'Extracted':r.error,r.ok?'ok':'err');loadFiles(cwd);}
      else if(act==='copy'){const nn=await prompt2('Copy to','Destination',p+'.copy');
        if(!nn)return;const r=await postJSON('/api/file/copy',{src:p,dst:nn});
        toast(r.ok?'Copied':r.error,r.ok?'ok':'err');loadFiles(cwd);}
      else if(act==='chmod'){const m=await prompt2('Change permissions','Mode',
          row.querySelector('td:nth-child(3)').textContent.trim());
        if(!m)return;const r=await postJSON('/api/file/chmod',{path:p,mode:m});
        toast(r.ok?'Permissions updated':r.error,r.ok?'ok':'err');loadFiles(cwd);}
      else if(act==='ren'){const cur=p.split('/').pop();
        const nn=await prompt2('Rename','New name',cur);if(!nn)return;
        const r=await postJSON('/api/file/rename',{path:p,newname:nn});
        toast(r.ok?'Renamed':r.error,r.ok?'ok':'err');loadFiles(cwd);}
      else if(act==='del'){if(!confirm('Delete "'+p+'"?'))return;
        const r=await postJSON('/api/file/delete',{paths:[p]});
        toast(r.errors&&r.errors.length?r.errors[0]:'Deleted',
              r.errors&&r.errors.length?'err':'ok');loadFiles(cwd);}
    }));
  }catch(e){toast('Failed to load files','err');}
}
function renderCrumbs(p){
  const parts=p.split('/').filter(Boolean);
  let html=`<a data-p="/">🏠 root</a>`;let acc='';
  parts.forEach(seg=>{acc+='/'+seg;
    html+=`<span class="sep">/</span><a data-p="${esc(acc)}">${esc(seg)}</a>`;});
  const c=$('#crumbs');c.innerHTML=html;
  $$('#crumbs a').forEach(a=>a.addEventListener('click',()=>loadFiles(a.dataset.p)));
}
async function uploadFiles(list,dest){
  if(!list||!list.length)return;
  const fd=new FormData();fd.append('path',dest);
  for(const f of list)fd.append('files',f,f.webkitRelativePath||f.name);
  toast('Uploading '+list.length+' file(s)…');
  try{const r=await apiJSON('/api/file/upload',{method:'POST',body:fd});
    if(r.ok)toast('Uploaded '+r.count+' file(s)','ok');
    else toast(r.error||'Upload failed','err');
  }catch(e){toast('Upload failed','err');}
  loadFiles(dest);
}
$('#up-input').addEventListener('change',e=>{uploadFiles(e.target.files,cwd);e.target.value='';});
$('#up-dir').addEventListener('change',e=>{uploadFiles(e.target.files,cwd);e.target.value='';});
const drop=$('#drop');
['dragenter','dragover'].forEach(ev=>drop.addEventListener(ev,e=>{e.preventDefault();drop.classList.add('over');}));
['dragleave','drop'].forEach(ev=>drop.addEventListener(ev,e=>{e.preventDefault();drop.classList.remove('over');}));
drop.addEventListener('drop',e=>{e.preventDefault();
  if(e.dataTransfer.files.length)uploadFiles(e.dataTransfer.files,cwd);});
$('#btn-refresh').onclick=()=>loadFiles(cwd);
$('#btn-newfile').onclick=async()=>{
  const n=await prompt2('New file','File name','untitled.txt');if(!n)return;
  const r=await postJSON('/api/file/new',{path:(cwd==='/'?'':cwd)+'/'+n});
  toast(r.ok?'Created':r.error,r.ok?'ok':'err');loadFiles(cwd);};
$('#btn-newdir').onclick=async()=>{
  const n=await prompt2('New folder','Folder name','new-folder');if(!n)return;
  const r=await postJSON('/api/file/mkdir',{path:(cwd==='/'?'':cwd)+'/'+n});
  toast(r.ok?'Created':r.error,r.ok?'ok':'err');loadFiles(cwd);};
$('#btn-zip').onclick=()=>{location.href='/api/file/zip?path='+encodeURIComponent(cwd);};
$('#btn-search-toggle').onclick=()=>{const c=$('#search-card');
  c.style.display=c.style.display==='none'?'block':'none';};
$('#btn-search').onclick=async()=>{
  const q=$('#sq').value.trim();if(!q)return;
  const mode=$('#smode').value;
  const r=await apiJSON('/api/file/search?q='+encodeURIComponent(q)+
    '&mode='+mode+'&path='+encodeURIComponent(cwd));
  if(!r.ok){toast(r.error,'err');return;}
  const box=$('#search-results');
  if(!r.results.length){box.innerHTML='<div class="dim">no matches</div>';return;}
  box.innerHTML=r.results.map(x=>`
    <div style="padding:4px 0;border-bottom:1px solid #131b25;font-size:12px">
      <a style="color:var(--accent);cursor:pointer" data-goto="${esc(x.path)}" data-dir="${x.dir}">
        ${esc(x.path)}</a>
      <span class="dim"> ${x.dir?'':(x.size_h||'')}</span></div>`).join('');
  $$('#search-results a').forEach(a=>a.addEventListener('click',()=>{
    if(a.dataset.dir==='true')loadFiles(a.dataset.goto);else openEditor(a.dataset.goto);}));
};

let editingPath=null;
async function openEditor(path){
  try{const d=await apiJSON('/api/file?path='+encodeURIComponent(path));
    if(!d.ok){toast(d.error||'Cannot open','err');return;}
    editingPath=d.path;
    if(!$('#v-edit')){
      const s=document.createElement('section');s.className='view';s.id='v-edit';
      s.innerHTML=`<h2 class="title">Text Editor</h2>
        <p class="desc">Editing: <span class="mono" id="ed-path">—</span></p>
        <div class="row" style="margin-bottom:11px">
          <button class="btn primary" id="btn-save">💾 Save</button>
          <button class="btn" id="btn-dl-ed">⤓ Download</button>
          <span class="spacer"></span>
          <span class="muted" id="ed-status" style="font-size:11.5px"></span>
        </div>
        <textarea id="editor" spellcheck="false"></textarea>`;
      $('#main').appendChild(s);
      $('#btn-save').onclick=doSave;
      $('#btn-dl-ed').onclick=()=>{if(editingPath)
        location.href='/api/file/download?path='+encodeURIComponent(editingPath);};
      $('#editor').addEventListener('keydown',e=>{
        if(e.key==='Tab'){e.preventDefault();const t=e.target,s=t.selectionStart,en=t.selectionEnd;
          t.value=t.value.substring(0,s)+'    '+t.value.substring(en);
          t.selectionStart=t.selectionEnd=s+4;}
        if((e.ctrlKey||e.metaKey)&&e.key==='s'){e.preventDefault();doSave();}});
    }
    $('#ed-path').textContent=d.path;
    $('#editor').value=d.content;
    $('#ed-status').textContent=fmtBytes(d.size)+' · UTF-8';
    $$('.nav').forEach(x=>x.classList.remove('active'));
    $$('.view').forEach(v=>v.classList.remove('active'));
    $('#v-edit').classList.add('active');currentView='edit';
  }catch(e){toast('Failed to open','err');}
}
async function doSave(){
  if(!editingPath){toast('No file open','err');return;}
  const r=await postJSON('/api/file/save',{path:editingPath,content:$('#editor').value});
  toast(r.ok?'Saved':r.error,r.ok?'ok':'err');
  if(r.ok)$('#ed-status').textContent='saved just now';
}

/* ============================================================================
   Terminal (xterm.js + real PTY)
   ========================================================================= */
let xterm = null;
let fitAddon = null;
let shellReady = false;
let readAbort = null;

function ensureTerm() {
  if (xterm) return;
  const el = document.getElementById('term');
  if (!el) return;
  if (typeof Terminal === 'undefined') {
    el.innerHTML = '<div style="padding:20px;color:#ff5c5c">xterm.js failed to load (CDN blocked?). Terminal unavailable.</div>';
    return;
  }

  xterm = new Terminal({
    cursorBlink: true,
    fontFamily: 'ui-monospace, SFMono-Regular, Menlo, Consolas, monospace',
    fontSize: 13,
    lineHeight: 1.2,
    theme: {
      background: '#05080c',
      foreground: '#d7e0ea',
      cursor: '#3ea6ff',
      selectionBackground: '#1f3a55',
      black:   '#1c2531', red:     '#ff5c5c',
      green:   '#2ecc71', yellow:  '#f5a623',
      blue:    '#3ea6ff', magenta: '#a67cff',
      cyan:    '#56d4dd', white:   '#d7e0ea',
      brightBlack:   '#4a5768', brightRed:     '#ff8080',
      brightGreen:   '#5ce49b', brightYellow:  '#ffc754',
      brightBlue:    '#7bc3ff', brightMagenta: '#c4a6ff',
      brightCyan:    '#7de5ec', brightWhite:   '#ffffff',
    },
    scrollback: 5000,
    allowProposedApi: true,
  });

  fitAddon = new FitAddon.FitAddon();
  xterm.loadAddon(fitAddon);
  xterm.open(el);

  xterm.onData(data => {
    if (!shellReady) return;
    postJSON('/api/shell/write', { data });
  });

  xterm.onResize(({ rows, cols }) => {
    if (!shellReady) return;
    postJSON('/api/shell/resize', { rows, cols });
  });

  setTimeout(() => {
    try { fitAddon.fit(); } catch (e) {}
    xterm.focus();
  }, 60);
}

async function initShell() {
  ensureTerm();
  if (!xterm) return;
  try {
    const r = await postJSON('/api/shell/spawn', {});
    if (!r.ok) { toast('Shell spawn failed', 'err'); return; }
    shellReady = true;
    setTermStatus('shell: ' + r.sid.slice(0, 8) + '  ·  connected');
    readLoop();
    xterm.focus();
  } catch (e) {
    toast('Shell init error', 'err');
  }
}

async function readLoop() {
  if (readAbort) { try { readAbort.abort(); } catch (e) {} }
  readAbort = new AbortController();

  while (shellReady) {
    try {
      const r = await fetch('/api/shell/read', {
        credentials: 'same-origin',
        signal: readAbort.signal,
      });
      if (r.status === 401) { location.href = '/login'; return; }
      const buf = await r.arrayBuffer();
      if (buf.byteLength && xterm) {
        xterm.write(new Uint8Array(buf));
      }
    } catch (e) {
      if (e.name === 'AbortError') return;
      await new Promise(res => setTimeout(res, 400));
    }
  }
}

function setTermStatus(t) {
  const el = document.getElementById('term-status');
  if (el) el.textContent = t;
}

document.getElementById('btn-clear').onclick = () => {
  if (xterm) { xterm.clear(); xterm.write('\x1b[2J\x1b[H'); }
};

document.getElementById('btn-kill-shell').onclick = async () => {
  await postJSON('/api/shell/kill', {});
  shellReady = false;
  if (readAbort) try { readAbort.abort(); } catch (e) {}
  setTermStatus('shell killed');
  if (xterm) { xterm.clear(); xterm.write('\x1b[2J\x1b[H'); }
  toast('Shell killed', 'ok');
  setTimeout(initShell, 300);
};

window.addEventListener('resize', () => {
  if (fitAddon && xterm) {
    try { fitAddon.fit(); } catch (e) {}
  }
});
document.addEventListener('visibilitychange', () => {
  if (!document.hidden && fitAddon && xterm) {
    try { fitAddon.fit(); } catch (e) {}
  }
});

async function loadProcs(){
  try{const d=await apiJSON('/api/processes');
    const body=$('#proc-body');
    if(!d.processes||!d.processes.length){
      body.innerHTML='<tr><td colspan="7" class="empty">psutil unavailable</td></tr>';return;}
    body.innerHTML=d.processes.map(p=>`
      <tr><td class="dim">${p.pid}</td>
      <td>${esc(p.name)}${p.cmd?`<div class="dim" style="font-size:10px;max-width:320px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap">${esc(p.cmd)}</div>`:''}</td>
      <td class="muted">${esc(p.user||'—')}</td>
      <td><span class="pill ${p.status==='running'?'g':'b'}">${esc(p.status||'?')}</span></td>
      <td style="text-align:right" class="muted">${p.cpu}</td>
      <td style="text-align:right" class="muted">${p.mem}</td>
      <td style="text-align:right">
        <button class="btn sm" data-sig="HUP" data-pid="${p.pid}">HUP</button>
        <button class="btn sm" data-sig="TERM" data-pid="${p.pid}">TERM</button>
        <button class="btn sm danger" data-sig="KILL" data-pid="${p.pid}">KILL</button>
      </td></tr>`).join('');
    $$('#proc-body button[data-sig]').forEach(b=>b.addEventListener('click',async()=>{
      const pid=b.dataset.pid,sig=b.dataset.sig;
      if(sig==='KILL'&&!confirm('SIGKILL PID '+pid+'?'))return;
      const r=await postJSON('/api/process/kill',{pid:Number(pid),signal:sig});
      toast(r.ok?r.message:r.error,r.ok?'ok':'err');loadProcs();}));
  }catch(e){}
}
$('#btn-proc-refresh').onclick=loadProcs;
$('#btn-proc-tree').onclick=async()=>{
  const t=$('#tree-view');t.style.display=t.style.display==='none'?'block':'none';
  if(t.style.display==='none')return;
  const d=await apiJSON('/api/process/tree');
  function render(nodes,depth=0){
    return nodes.map(n=>`<div style="padding-left:${depth*18}px">└─ ${esc(n.name)} <span class="dim">#${n.pid}</span></div>`+
      render(n.children||[],depth+1)).join('');}
  $('#tree-content').innerHTML=render(d.tree||[])||'<span class="dim">no data</span>';};

async function loadSites(){
  try{const d=await apiJSON('/api/sites');
    const body=$('#sites-body');
    if(!d.sites.length){body.innerHTML='<tr><td colspan="5" class="empty">no sites yet</td></tr>';return;}
    body.innerHTML=d.sites.map(s=>`
      <tr><td><b>${esc(s.name)}</b> ${s.spa?'<span class="pill b">SPA</span>':''}
          ${s.exists?'':'<span class="pill r">missing dir</span>'}</td>
        <td class="muted">${esc(s.dir)}</td>
        <td><a href="${esc(s.url)}" target="_blank" style="color:var(--accent)">${esc(s.url)}</a></td>
        <td class="dim">${esc(s.size_h)}</td>
        <td style="text-align:right">
          <button class="btn sm" data-open="${esc(s.url)}">open</button>
          <button class="btn sm" data-browse="${esc(s.dir)}">files</button>
          <button class="btn sm danger" data-del="${esc(s.name)}">delete</button>
        </td></tr>`).join('');
    $$('#sites-body button').forEach(b=>b.addEventListener('click',async()=>{
      if(b.dataset.open)window.open(b.dataset.open,'_blank');
      if(b.dataset.browse){
        $$('.nav').forEach(x=>x.classList.remove('active'));
        document.querySelector('.nav[data-view="files"]').classList.add('active');
        $$('.view').forEach(v=>v.classList.remove('active'));
        $('#v-files').classList.add('active');currentView='files';
        loadFiles('/'+b.dataset.browse);}
      if(b.dataset.del){if(!confirm('Delete site "'+b.dataset.del+'"?'))return;
        const r=await api('/api/sites/'+encodeURIComponent(b.dataset.del),{method:'DELETE'});
        const j=await r.json();
        toast(j.ok?'Site deleted':(j.error||'Error'),j.ok?'ok':'err');loadSites();}
    }));
  }catch(e){}
}
$('#btn-site-add').onclick=async()=>{
  const name=$('#st-name').value.trim();
  const dir=$('#st-dir').value.trim()||name;
  const index=$('#st-index').value.trim()||'index.html';
  const spa=$('#st-spa').value==='1';
  if(!name){toast('Site name required','err');return;}
  const r=await postJSON('/api/sites',{name,dir,index,spa});
  if(r.ok){toast('Created at '+r.url,'ok');
    $('#st-name').value='';$('#st-dir').value='';loadSites();}
  else toast(r.error,'err');};

async function loadCron(){
  try{const d=await apiJSON('/api/cron');
    const body=$('#cron-body');
    if(!d.jobs.length){body.innerHTML='<tr><td colspan="6" class="empty">no jobs</td></tr>';return;}
    body.innerHTML=d.jobs.map(j=>`
      <tr><td>${esc(j.name)} ${j.running?'<span class="pill a">running</span>':''}</td>
        <td class="dim" style="max-width:260px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap">${esc(j.cmd)}</td>
        <td class="muted">${j.interval}s</td>
        <td class="dim">${j.last_run?new Date(j.last_run*1000).toLocaleString():'—'}</td>
        <td>${j.last_code!==undefined?`<span class="pill ${j.last_code===0?'g':'r'}">${j.last_code}</span>`:''}</td>
        <td style="text-align:right">
          <button class="btn sm" data-run="${j.id}">run</button>
          <button class="btn sm" data-out="${j.id}" data-name="${esc(j.name)}">out</button>
          <button class="btn sm" data-toggle="${j.id}">${j.enabled?'disable':'enable'}</button>
          <button class="btn sm danger" data-del="${j.id}">delete</button>
        </td></tr>`).join('');
    $$('#cron-body button').forEach(b=>b.addEventListener('click',async()=>{
      if(b.dataset.run){await postJSON('/api/cron/'+b.dataset.run+'/run',{});
        toast('Running','ok');loadCron();}
      if(b.dataset.toggle){await postJSON('/api/cron/'+b.dataset.toggle+'/toggle',{});loadCron();}
      if(b.dataset.del){if(!confirm('Delete job?'))return;
        await api('/api/cron/'+b.dataset.del,{method:'DELETE'});loadCron();}
      if(b.dataset.out){const r=await apiJSON('/api/cron/'+b.dataset.out+'/output');
        const card=$('#cron-output-card');card.style.display='block';
        $('#cron-output-name').textContent=b.dataset.name;
        $('#cron-output').textContent=(r.runs||[]).map(x=>
          `[${new Date(x.time*1000).toLocaleString()}] exit=${x.code} (${x.duration}s)\n${x.stdout||''}${x.stderr?'\n[stderr]\n'+x.stderr:''}`
        ).join('\n\n')||'no runs yet';}
    }));
  }catch(e){}
}
$('#btn-cron-add').onclick=async()=>{
  const name=$('#cj-name').value.trim()||'job';
  const cmd=$('#cj-cmd').value.trim();
  const interval=Number($('#cj-int').value||300);
  const r=await postJSON('/api/cron',{name,cmd,interval});
  if(r.ok){toast('Job added','ok');$('#cj-name').value='';$('#cj-cmd').value='';loadCron();}
  else toast(r.error,'err');};
$('#btn-cron-output-close').onclick=()=>{$('#cron-output-card').style.display='none';};

async function loadBackups(){
  try{const d=await apiJSON('/api/backup/list');
    const body=$('#backup-body');
    if(!d.backups.length){body.innerHTML='<tr><td colspan="4" class="empty">no backups</td></tr>';return;}
    body.innerHTML=d.backups.map(b=>`
      <tr><td>${esc(b.name)}</td><td class="muted">${esc(b.size_h)}</td>
        <td class="dim">${esc(b.mtime_h)}</td>
        <td style="text-align:right">
          <button class="btn sm" data-dl="${esc(b.name)}">download</button>
          <button class="btn sm" data-rs="${esc(b.name)}">restore</button>
          <button class="btn sm danger" data-del="${esc(b.name)}">delete</button>
        </td></tr>`).join('');
    $$('#backup-body button').forEach(btn=>btn.addEventListener('click',async()=>{
      if(btn.dataset.dl)location.href='/api/backup/download/'+encodeURIComponent(btn.dataset.dl);
      if(btn.dataset.del){if(!confirm('Delete backup?'))return;
        await postJSON('/api/backup/delete',{name:btn.dataset.del});loadBackups();}
      if(btn.dataset.rs){if(!confirm('Restore backup? This REPLACES your current files!'))return;
        const r=await postJSON('/api/backup/restore',{name:btn.dataset.rs});
        toast(r.ok?'Restored':r.error,r.ok?'ok':'err');loadFiles('/');}
    }));
  }catch(e){}
}
$('#btn-backup-create').onclick=async()=>{toast('Creating backup…');
  const r=await postJSON('/api/backup/create',{});
  toast(r.ok?'Created '+r.size_h:r.error,r.ok?'ok':'err');loadBackups();};
$('#btn-backup-refresh').onclick=loadBackups;

let currentLog=null;
async function loadLogs(){
  try{const d=await apiJSON('/api/logs');
    const body=$('#logs-body');
    if(!d.logs.length){body.innerHTML='<tr><td colspan="2" class="empty">no logs</td></tr>';return;}
    body.innerHTML=d.logs.map(l=>`
      <tr data-path="${esc(l.path)}" data-name="${esc(l.name)}" style="cursor:pointer">
        <td>${esc(l.name)}</td><td class="muted" style="text-align:right">${fmtBytes(l.size)}</td>
      </tr>`).join('');
    $$('#logs-body tr').forEach(tr=>tr.addEventListener('click',()=>openLog(tr.dataset.path,tr.dataset.name)));
  }catch(e){}
}
async function openLog(path,name){
  currentLog=path;$('#log-title').textContent=name;
  const r=await apiJSON('/api/logs/read?path='+encodeURIComponent(path));
  if(!r.ok){$('#log-content').textContent='error: '+r.error;return;}
  $('#log-content').textContent=r.content||'(empty)';
}
$('#btn-log-refresh').onclick=()=>{if(currentLog)openLog(currentLog,$('#log-title').textContent);};

async function loadEnv(){
  try{const d=await apiJSON('/api/system/env');
    const cust=$('#env-custom');
    const entries=Object.entries(d.custom||{});
    cust.innerHTML=entries.length?entries.map(([k,v])=>`
      <tr><td>${esc(k)}</td><td class="muted">${esc(v)}</td>
      <td style="text-align:right"><button class="btn sm danger" data-k="${esc(k)}">✕</button></td></tr>`
    ).join(''):'<tr><td colspan="3" class="empty">none</td></tr>';
    $$('#env-custom button').forEach(b=>b.addEventListener('click',async()=>{
      await postJSON('/api/system/env',{delete:b.dataset.k});loadEnv();}));
    const sys=$('#env-system');
    sys.innerHTML=Object.entries(d.system||{}).map(([k,v])=>
      `<tr><td class="muted">${esc(k)}</td><td>${esc(v)}</td></tr>`).join('');
  }catch(e){}
}
$('#btn-env-set').onclick=async()=>{
  const k=$('#env-key').value.trim(),v=$('#env-val').value;
  if(!k)return;await postJSON('/api/system/env',{key:k,value:v});
  $('#env-key').value='';$('#env-val').value='';loadEnv();};

async function loadUsers(){
  try{const d=await apiJSON('/api/users');
    const body=$('#users-body');
    if(!d.ok){body.innerHTML='<tr><td colspan="4" class="empty">admin only</td></tr>';return;}
    body.innerHTML=d.users.map(u=>`
      <tr><td><b>${esc(u.username)}</b></td>
        <td><span class="pill ${u.role==='admin'?'a':'b'}">${esc(u.role)}</span></td>
        <td class="dim">${u.created?new Date(u.created*1000).toLocaleString():'—'}</td>
        <td style="text-align:right">
          <button class="btn sm danger" data-del="${esc(u.username)}">delete</button>
        </td></tr>`).join('');
    $$('#users-body button').forEach(b=>b.addEventListener('click',async()=>{
      if(!confirm('Delete user '+b.dataset.del+'?'))return;
      const r=await api('/api/users/'+encodeURIComponent(b.dataset.del),{method:'DELETE'});
      const j=await r.json();
      toast(j.ok?'Deleted':j.error,j.ok?'ok':'err');loadUsers();}));
  }catch(e){}
}
$('#btn-usr-add').onclick=async()=>{
  const u=$('#usr-name').value.trim(),p=$('#usr-pass').value,role=$('#usr-role').value;
  if(!u||!p){toast('Username and password required','err');return;}
  const r=await postJSON('/api/users',{username:u,password:p,role});
  toast(r.ok?'User created':r.error,r.ok?'ok':'err');
  if(r.ok){$('#usr-name').value='';$('#usr-pass').value='';loadUsers();}};
$('#btn-pw').onclick=async()=>{
  const oldp=$('#pw-old').value,newp=$('#pw-new').value;
  const r=await postJSON('/api/users/password',{old:oldp,new:newp});
  toast(r.ok?'Password changed':r.error,r.ok?'ok':'err');
  if(r.ok){$('#pw-old').value='';$('#pw-new').value='';}};

async function loadSysFull(){
  try{const d=await apiJSON('/api/system/info');
    const rows=[
      ['Hostname',d.hostname],['System',d.system],['Release',d.release],
      ['Version',d.version],['Machine',d.machine],['Processor',d.processor],
      ['Python',(d.python||'').split('\n')[0]],
      ['Python exe',d.python_exe],['PID',d.pid],['Parent PID',d.ppid],
      ['User',d.user],['CWD',d.cwd],['Env vars',d.env_count],
      ['Data dir',d.data_dir],['Ephemeral',String(d.ephemeral)],
    ];
    if(d.render){
      rows.push(['Render service',d.render.service_name]);
      rows.push(['Render type',d.render.service_type]);
      rows.push(['Render region',d.render.region]);
      rows.push(['External URL',d.render.external_url]);
      rows.push(['Instance ID',d.render.instance_id]);
    }
    let html=rows.map(r=>`<div>${esc(r[0])}</div><div>${esc(r[1])}</div>`).join('');
    if(d.mounts&&d.mounts.length){
      html+=`<div style="grid-column:1/-1;padding-top:12px;color:var(--accent)">Mounted filesystems</div>`;
      html+=d.mounts.map(m=>
        `<div class="dim">${esc(m.device)}</div><div>${esc(m.mountpoint)} <span class="dim">(${esc(m.fstype)})</span></div>`
      ).join('');}
    if(d.interfaces){
      html+=`<div style="grid-column:1/-1;padding-top:12px;color:var(--accent)">Interfaces</div>`;
      for(const [k,v] of Object.entries(d.interfaces)){
        html+=`<div class="dim">${esc(k)}</div><div>${v.map(esc).join(', ')||'—'}</div>`;}
    }
    $('#sysinfo-full').innerHTML=html;
  }catch(e){}
}
$('#btn-sys-refresh').onclick=loadSysFull;

let pipPackages=[];
async function loadPip(){
  try{const d=await apiJSON('/api/pip/list');
    pipPackages=d.packages||[];renderPip();
  }catch(e){}
}
function renderPip(){
  const q=($('#pip-filter').value||'').toLowerCase();
  const list=pipPackages.filter(p=>!q||p.name.toLowerCase().includes(q));
  $('#pip-body').innerHTML=list.map(p=>
    `<tr><td>${esc(p.name)}</td><td class="muted">${esc(p.version)}</td></tr>`).join('')
    ||'<tr><td colspan="2" class="empty">no packages</td></tr>';
}
$('#btn-pip-refresh').onclick=loadPip;
$('#pip-filter').addEventListener('input',renderPip);
$('#btn-pip-install').onclick=async()=>{
  const raw=$('#pip-pkg').value.trim();if(!raw)return;
  const pkgs=raw.split(/[,\s]+/).filter(Boolean);
  $('#pip-log').style.display='block';
  $('#pip-log').textContent='Installing '+pkgs.join(', ')+'…';
  const r=await postJSON('/api/pip/install',{packages:pkgs});
  $('#pip-log').textContent=(r.stdout||'')+(r.stderr?'\n[stderr]\n'+r.stderr:'');
  toast(r.ok?'Installed':r.error,r.ok?'ok':'err');loadPip();};
$('#btn-pip-uninstall').onclick=async()=>{
  const raw=$('#pip-pkg').value.trim();if(!raw)return;
  if(!confirm('Uninstall '+raw+'?'))return;
  const pkgs=raw.split(/[,\s]+/).filter(Boolean);
  const r=await postJSON('/api/pip/uninstall',{packages:pkgs});
  $('#pip-log').style.display='block';
  $('#pip-log').textContent=(r.stdout||'')+(r.stderr?'\n'+r.stderr:'');
  toast(r.ok?'Done':r.error,r.ok?'ok':'err');loadPip();};

$('#btn-ping').onclick=async()=>{
  const host=$('#pg-host').value.trim();if(!host)return;
  $('#pg-out').style.display='block';$('#pg-out').textContent='pinging…';
  const r=await postJSON('/api/network/ping',{host});
  $('#pg-out').textContent=(r.stdout||'')+(r.stderr||'');};
$('#btn-dns').onclick=async()=>{
  const host=$('#dns-host').value.trim();if(!host)return;
  const r=await postJSON('/api/network/dns',{host});
  if(!r.ok){$('#dns-out').innerHTML='<span style="color:var(--red)">'+esc(r.error)+'</span>';return;}
  $('#dns-out').innerHTML=(r.records||[]).map(x=>
    `<div>${esc(x.family)} <b>${esc(x.ip)}</b></div>`).join('')||'<span class="dim">no records</span>';};
$('#btn-curl').onclick=async()=>{
  const url=$('#curl-url').value.trim();if(!url)return;
  $('#curl-out').style.display='block';$('#curl-out').textContent='fetching…';
  const r=await postJSON('/api/network/curl',{url,method:$('#curl-m').value});
  if(!r.ok){$('#curl-out').textContent='error: '+r.error;return;}
  const head='HTTP '+r.status+'\n'+Object.entries(r.headers||{}).map(([k,v])=>k+': '+v).join('\n');
  $('#curl-out').textContent=head+'\n\n'+(r.body||'').slice(0,20000);};
$('#btn-pubip').onclick=async()=>{
  const r=await apiJSON('/api/network/publicip');
  $('#pubip-out').textContent=r.ok?r.ip:('error: '+r.error);};
async function loadPorts(){
  const r=await apiJSON('/api/network/ports');
  $('#ports-body').innerHTML=(r.listening||[]).map(p=>
    `<tr><td><b>${p.port}</b></td><td class="dim">${esc(p.ip)}</td>
     <td class="dim">${p.pid||'—'}</td><td>${esc(p.process||'—')}</td></tr>`).join('')
    ||'<tr><td colspan="4" class="empty">no listening sockets</td></tr>';}
async function loadIfaces(){
  const r=await apiJSON('/api/network/interfaces');
  const out=Object.entries(r.interfaces||{}).map(([name,v])=>{
    const addrs=(v.addresses||[]).filter(a=>a.family.includes('AF_INET')||a.family.includes('2'))
      .map(a=>a.address).join(', ');
    return `<div style="padding:5px 0;border-bottom:1px solid #131b25">
      <b>${esc(name)}</b> ${v.up?'<span class="pill g">up</span>':'<span class="pill r">down</span>'}
      <div class="dim" style="font-size:11px">${esc(addrs||'—')}</div></div>`;}).join('');
  $('#ifaces-out').innerHTML=out||'<span class="dim">no interfaces</span>';}
$('#btn-ports').onclick=loadPorts;
$('#btn-ifaces').onclick=loadIfaces;

loadStats();loadDashProcs();loadFiles('/');
ensureTerm();initShell();
setInterval(()=>{if(currentView==='dash'){loadStats();loadDashProcs();}},3000);
setInterval(()=>{if(currentView==='proc')loadProcs();},5000);
setInterval(()=>{if(currentView==='cron')loadCron();},7000);

document.addEventListener('keydown',e=>{
  if((e.ctrlKey||e.metaKey)&&e.key==='k'){e.preventDefault();
    document.querySelector('.nav[data-view="term"]').click();}});
window.addEventListener('resize',()=>{
  if(shellReady&&xterm&&fitAddon){
    try{fitAddon.fit();}catch(e){}}
});
</script>
</body>
</html>"""

# ==============================================================================
#  BOOT
# ==============================================================================
def _banner():
    line = "=" * 70
    print(line)
    print(f"  {APP_NAME} v{VERSION}  —  single-file VPS  (Render edition)")
    print(line)
    users = load_users()
    print(f"  Platform       : {'Render' if IS_RENDER else 'Generic'}")
    print(f"  Data directory : {DATA_DIR}"
          f"{'  [EPHEMERAL — set DATA_DIR + add a Disk!]' if EPHEMERAL_DATA else '  [persistent]'}")
    print(f"  File root      : {FILES_DIR}")
    print(f"  Backups        : {BACKUP_DIR}")
    print(f"  Logs           : {LOGS_DIR}")
    print(f"  Users          : {', '.join(users.keys())}")
    print(f"  psutil         : {'available' if psutil else 'MISSING (degraded stats)'}")
    print(f"  PTY support    : {'yes' if hasattr(os, 'openpty') else 'no'}")
    if IS_RENDER:
        print(f"  Render service : {os.environ.get('RENDER_SERVICE_NAME', '?')}")
        print(f"  Render URL     : {os.environ.get('RENDER_EXTERNAL_URL', '?')}")
    if USING_DEFAULT_PASSWORD:
        print("  !! WARNING: VPS_PASSWORD not set — using default 'railway'")
    if EPHEMERAL_DATA:
        print("  !! WARNING: data dir looks ephemeral.  On Render, add a Disk")
        print("             mounted at /var/data, then set DATA_DIR=/var/data.")
    print(line)
    print("  Open your Render URL and log in.")
    print(line)


_banner()


if __name__ == "__main__":
    port = int(os.environ.get("PORT", 10000))
    app.run(host="0.0.0.0", port=port, debug=False, threaded=True)
