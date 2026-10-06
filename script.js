"use strict";
(function () {
  var $ = function (id) { return document.getElementById(id); };
  var feed = $("feed"), multEl = $("mult"), lvlEl = $("lvl"), chainEl = $("chain"),
      msgEl = $("msg"), q = $("q"), form = $("sf");

  /* ---------- state (everything BigInt, nothing bounded) ---------- */
  var level = 0;          // doubling level
  var scale = 1n;         // 2^level, current multiplier
  var firstId = 0n, lastId = -1n, focus = 0n;
  var busy = false;
  var MAXC = 24;          // max cards kept in the DOM
  var reduce = window.matchMedia && matchMedia("(prefers-reduced-motion: reduce)").matches;

  /* ---------- word pools ---------- */
  var BASE = {
    s: ["Vy","Ae","Qor","Zel","Thy","Ny","Kael","Orv","Xen","Ish","Lum","Dra","Sel","Mor","Eth","Vael","Ryn","Cael","Ul","Tor","Phae","Zy","Obs","Kyr","Nor","Il","Ves","Hex","Aur","Syl","Bra","Cyr","Dyn","Fel","Gal","Jor"],
    m: ["a","e","i","o","u","ae","y","ar","en","il","or","un","ix","ra","lo","the","qui","ze","na","mi","ro","vi"],
    e: ["rix","lon","vane","thar","nyx","mere","dor","quin","lith","zara","phen","mox","gar","vyn","sel","tris","ius","ora","ex","un","wyn","th","ar","ion"],
    w1: ["Obsidian","Hollow","Silent","Glass","Pale","Static","Mirror","Lunar","Frozen","Veiled","Quiet","Iron","Silver","Drift","Tidal","Null","Distant","Folded","Shallow","Ashen","Echo","Velvet","Paper","Salt"],
    w2: ["Reach","Atoll","Basin","Spire","Orbit","Meridian","Expanse","Cradle","Shelf","Garden","Archive","Harbor","Lattice","Terrace","Vault","Delta","Crown","Threshold","Tide","Span"],
    dims: ["Folded","Mirrored","Nested","Slow","Dense","Hollow","Parallel","Recursive","Tilted","Quiet","Braided","Layered"],
    classes: ["Primordial","Dormant","Ascendant","Luminous","Recursive","Anomalous","Archival","Sovereign","Tidal","Cryptic","Stable","Fractal"],
    types: ["Civilization","Collective","Swarm intelligence","Machine lineage","Crystal colony","Wandering fleet","Hive archive","Tidal species","Signal-born entity","Memory organism","Orbital federation","Living city","Dream ecology","Weather-mind","Stone choir","Doubling cult"],
    dv: ["Detected","Mapped","Decoded","Unfolded","Catalogued","Traced","Reconstructed","Measured","Awakened","Recovered"],
    dobj: ["a self-copying signal","a lattice that counts itself","a tide of identical moons","an archive written in doublings","a city that replicates at dusk","a resonance repeating twice per breath","a map that grows when observed","a silent twin of its own sky","a library of mirrored libraries","a number that refuses to end"],
    dpl: ["beneath the third horizon","inside a frozen echo","along the edge of the fold","within a quiet orbit","beyond every measured gate","under a sky that counts","between two identical tides","at the seam of two doublings"],
    da: ["Its members","Its structures","Its signals","Its memories","Its rulers","Its rivers of light"],
    db: ["split in two at every threshold","double with each passing cycle","echo into neighboring dimensions","repeat until they fill the sky","refuse to settle on a final form","carry a copy of themselves forward"],
    dc: ["Visitors report","Observers record","Archivists note","Cartographers claim"],
    dd: ["no edge to its borders.","a count that never closes.","a quiet hum in every doubled hall.","that its map keeps growing as it is read.","no final record of its history."],
    sym: ["⟁","⌬","⍟","◈","◇","⬡","⏣","⎔","✧","⊛","⟐","⧫","⬢","⌖","⍜","⨂","⟡","◬","⧖","⎊"],
    names: [], worlds: [], dimensions: [], cls: [], tp: [], disc: []
  };
  var POOL = {};
  function resetPool() { for (var k in BASE) POOL[k] = BASE[k].slice(); }
  resetPool();

  /* ---------- BigInt -> deterministic RNG ---------- */
  function seed(id) {
    var s = id < 0n ? ((-id) << 1n) | 1n : id << 1n;
    var x = s.toString(16);
    var a = 0x9E3779B9 | 0, b = 0x243F6A88 | 0, c = 0xB7E15162 | 0, d = 0x71374491 | 0;
    for (var i = x.length; i > 0; i -= 8) {
      var v = parseInt(x.slice(Math.max(0, i - 8), i), 16) | 0;
      a = Math.imul(a ^ v, 0x85EBCA6B); a ^= a >>> 13;
      b = Math.imul((b + v) | 0, 0xC2B2AE35) ^ a; b ^= b >>> 16;
      c = (Math.imul(c ^ b, 0x27D4EB2F) + v) | 0;
      d = Math.imul((d + c) | 0, 0x165667B1) ^ (a >>> 7);
      var t = a; a = b; b = c; c = d; d = t;
    }
    for (var j = 0; j < 3; j++) {
      a = Math.imul(a ^ (a >>> 16), 0x85EBCA6B) ^ b;
      b = Math.imul(b ^ (b >>> 13), 0xC2B2AE35) ^ c;
      c = Math.imul(c ^ (c >>> 16), 0x27D4EB2F) ^ d;
      d = Math.imul(d ^ (d >>> 15), 0x165667B1) ^ a;
    }
    return [a, b, c, d];
  }
  function rng(h) {
    var a = h[0], b = h[1], c = h[2], d = h[3];
    var f = function () {
      a |= 0; b |= 0; c |= 0; d |= 0;
      var t = (a + b | 0) + d | 0;
      d = d + 1 | 0; a = b ^ b >>> 9; b = c + (c << 3) | 0;
      c = (c << 21 | c >>> 11); c = c + t | 0;
      return (t >>> 0) / 4294967296;
    };
    for (var i = 0; i < 16; i++) f();
    return f;
  }
  function pick(r, arr) { return arr[Math.floor(r() * arr.length)]; }
  function cap(s) { return s.charAt(0).toUpperCase() + s.slice(1).toLowerCase(); }
  function hex8(n) { return (n >>> 0).toString(16).padStart(8, "0").toUpperCase(); }
  function word(r) {
    var s = pick(r, POOL.s), m = pick(r, POOL.m), m2 = pick(r, POOL.m), e = pick(r, POOL.e);
    var two = r() < 0.5, useC = r() < 0.2, c = POOL.names.length ? pick(r, POOL.names) : "";
    if (useC && c) return c;
    return cap(s + m + (two ? m2 : "") + e);
  }

  /* ---------- profile = pure function of BigInt ID ---------- */
  function profile(id) {
    var h = seed(id), r = rng(h);
    var w1 = word(r), w2 = word(r), has2 = r() < 0.75;
    var p = {};
    p.name = has2 ? w1 + " " + w2 : w1;
    p.world = pick(r, POOL.w1) + " " + pick(r, POOL.w2) + " " + (1 + Math.floor(r() * 9999));
    var wExtra = POOL.worlds.length ? pick(r, POOL.worlds) : "", wUse = r() < 0.15;
    if (wUse && wExtra) p.world = wExtra;
    p.dimension = pick(r, POOL.dims) + " Dimension D-" + (1000 + Math.floor(r() * 90000));
    var dExtra = POOL.dimensions.length ? pick(r, POOL.dimensions) : "", dUse = r() < 0.15;
    if (dUse && dExtra) p.dimension = dExtra;
    var L = "ABCDEFGHJKLMNPQRSTUVWXYZ";
    p.classification = pick(r, POOL.classes) + " · Class " + L.charAt(Math.floor(r() * L.length)) + Math.floor(r() * 99);
    var cExtra = POOL.cls.length ? pick(r, POOL.cls) : "", cUse = r() < 0.15;
    if (cUse && cExtra) p.classification = cExtra;
    p.type = pick(r, POOL.types);
    var tExtra = POOL.tp.length ? pick(r, POOL.tp) : "", tUse = r() < 0.15;
    if (tUse && tExtra) p.type = tExtra;
    var n = Math.floor(r() * 1000000);
    p.era = "Cycle " + (r() < 0.5 ? "−" : "+") + n.toLocaleString("en-US") + " from the First Doubling";
    p.discovery = pick(r, POOL.dv) + " " + pick(r, POOL.dobj) + " " + pick(r, POOL.dpl) + ".";
    var xExtra = POOL.disc.length ? pick(r, POOL.disc) : "", xUse = r() < 0.15;
    if (xUse && xExtra) p.discovery = xExtra;
    p.description = pick(r, POOL.da) + " " + pick(r, POOL.db) + ". " + pick(r, POOL.dc) + " " + pick(r, POOL.dd);
    p.symbol = pick(r, POOL.sym);
    p.code = "VX-" + hex8(h[0]) + "-" + hex8(h[1]);
    var o = OVR.get(id.toString());
    if (o) {
      for (var k in o) { if (k !== "id" && o[k]) p[k] = o[k]; }
    }
    return p;
  }

  /* ---------- optional data.txt ---------- */
  var OVR = new Map();
  var FIELDS = { name: 1, world: 1, dimension: 1, classification: 1, type: 1, era: 1, discovery: 1, description: 1, symbol: 1, code: 1 };
  var POOLKEYS = { names: "names", worlds: "worlds", dimensions: "dimensions", classes: "cls", types: "tp", discoveries: "disc", prefixes: "s", suffixes: "e" };
  function parseData(text) {
    var recs = text.split(/^[ \t]*-+[ \t]*$/m), used = 0;
    for (var i = 0; i < recs.length; i++) {
      var o = {}, lines = recs[i].split(/\r?\n/), any = false;
      for (var j = 0; j < lines.length; j++) {
        var ln = lines[j].trim();
        if (!ln || ln.charAt(0) === "#") continue;
        var k = ln.indexOf(":");
        if (k < 1) continue;
        o[ln.slice(0, k).trim().toLowerCase()] = ln.slice(k + 1).trim();
        any = true;
      }
      if (!any) continue;
      if (o.id && /^[+-]?\d+$/.test(o.id)) {
        var id = BigInt(o.id.replace(/^\+/, ""));
        var rec = {};
        if (o["class"]) o.classification = o["class"];
        for (var f in FIELDS) if (o[f]) rec[f] = o[f];
        OVR.set(id.toString(), rec); used++;
      } else {
        for (var pk in POOLKEYS) {
          if (o[pk]) {
            var items = o[pk].split("|").map(function (x) { return x.trim(); }).filter(Boolean);
            for (var m = 0; m < items.length; m++) POOL[POOLKEYS[pk]].push(items[m]);
            used++;
          }
        }
      }
    }
    return used;
  }

  /* ---------- formatting ---------- */
  function fmt(n) {
    var neg = n < 0n, s = (neg ? -n : n).toString();
    if (s.length <= 15) return (neg ? "−" : "") + s.replace(/\B(?=(\d{3})+(?!\d))/g, ",");
    return (neg ? "−" : "") + s.charAt(0) + "." + s.slice(1, 6) + "e+" + (s.length - 1);
  }
  function shortId(n, full) {
    var s = n.toString();
    if (full || s.length <= 60) return s;
    return s.slice(0, 28) + "…" + s.slice(-28) + "  (" + s.length + " digits)";
  }
  function say(t) { msgEl.textContent = t; }

  /* ---------- UI helpers ---------- */
  function el(tag, cls, text) {
    var e = document.createElement(tag);
    if (cls) e.className = cls;
    if (text !== undefined) e.textContent = text;
    return e;
  }
  function row(label, value) {
    var d = el("div", "f");
    d.append(el("span", "", label), el("div", "", value));
    return d;
  }
  function buildCard(id) {
    var p = profile(id), c = el("article", "card");
    c._id = id;
    var top = el("div", "top"), t = el("div", "");
    top.append(el("span", "sym", p.symbol));
    t.append(el("h2", "", p.name), el("p", "code", p.code));
    top.append(t);
    var idl = el("p", "id"), b = el("b", "", shortId(id, false));
    idl.append(document.createTextNode("ID "), b);
    idl.title = "Tap to show or shorten the full ID";
    idl._full = false;
    idl.onclick = function () { idl._full = !idl._full; b.textContent = shortId(id, idl._full); };
    c.append(top, idl,
      row("World", p.world), row("Dimension", p.dimension), row("Class", p.classification),
      row("Entity", p.type), row("Timeline", p.era), row("Discovery", p.discovery));
    c.append(el("p", "desc", p.description));
    var ech = el("div", "echo"), btn = el("button", "", "Open echo ↳");
    btn.type = "button"; btn.dataset.act = "echo"; btn.disabled = scale === 1n;
    ech.append(el("span", "", "Replicas ×" + fmt(scale)), btn);
    c.append(ech);
    return c;
  }

  /* ---------- scale display ---------- */
  function paint() {
    multEl.textContent = "×" + fmt(scale);
    multEl.title = scale.toString();
    var digits = scale.toString().length;
    lvlEl.textContent = "Level " + level + " · 2^" + level + (digits > 15 ? " · " + digits + " digits" : "");
    var parts = [], from = Math.max(0, level - 2);
    if (from > 0) parts.push("…");
    for (var i = from; i <= level + 3; i++) parts.push(fmt(1n << BigInt(i)));
    parts.push("…");
    chainEl.textContent = parts.join(" → ");
    multEl.classList.add("on");
    setTimeout(function () { multEl.classList.remove("on"); }, 350);
  }

  /* ---------- virtualized feed ---------- */
  function go(id) {
    busy = true;
    feed.textContent = "";
    var start = id - 2n, frag = document.createDocumentFragment();
    for (var i = 0n; i < 12n; i++) frag.append(buildCard(start + i));
    feed.append(frag);
    firstId = start; lastId = start + 11n; focus = id;
    var t = feed.children[2];
    t.classList.add("hit");
    setTimeout(function () { t.classList.remove("hit"); }, 1800);
    feed.scrollTop = Math.max(0, t.offsetTop - 8);
    busy = false;
    grow(); save();
  }
  function grow() {
    if (busy) return;
    busy = true;
    var n = 0, h = feed.clientHeight;
    while (n++ < 12 && feed.scrollHeight - feed.scrollTop - h < h * 1.5) {
      lastId += 1n; feed.append(buildCard(lastId));
    }
    n = 0;
    while (n++ < 12 && feed.scrollTop < h) {
      var before = feed.scrollHeight;
      firstId -= 1n; feed.prepend(buildCard(firstId));
      feed.scrollTop += feed.scrollHeight - before;
    }
    trim(h);
    busy = false;
  }
  function trim(h) {
    while (feed.children.length > MAXC) {
      var f = feed.firstElementChild, nx = f.nextElementSibling;
      if (f.offsetTop + f.offsetHeight < feed.scrollTop - h * 1.5) {
        var d = nx.offsetTop - f.offsetTop;
        f.remove(); feed.scrollTop -= d; firstId += 1n;
      } else {
        var l = feed.lastElementChild;
        if (l.offsetTop > feed.scrollTop + h * 4) { l.remove(); lastId -= 1n; }
        else break;
      }
    }
  }
  function updateFocus() {
    var st = feed.scrollTop + 12, kids = feed.children;
    for (var i = 0; i < kids.length; i++) {
      var c = kids[i];
      if (c.offsetTop + c.offsetHeight > st) {
        if (c._id !== focus) { focus = c._id; save(); }
        break;
      }
    }
  }
  var tick = false;
  feed.addEventListener("scroll", function () {
    if (tick || busy) return;
    tick = true;
    requestAnimationFrame(function () { tick = false; grow(); updateFocus(); });
  }, { passive: true });

  var saveT = 0;
  function save() {
    clearTimeout(saveT);
    saveT = setTimeout(function () {
      try { history.replaceState(null, "", "#" + level + ":" + focus.toString()); } catch (e) {}
    }, 300);
  }

  /* ---------- actions ---------- */
  function step(d) {
    var t = focus + d, kids = feed.children;
    for (var i = 0; i < kids.length; i++) {
      if (kids[i]._id === t) {
        feed.scrollTo({ top: Math.max(0, kids[i].offsetTop - 8), behavior: reduce ? "auto" : "smooth" });
        focus = t; save(); return;
      }
    }
    go(t);
  }
  function multiply() {
    var prev = scale;
    level += 1; scale <<= 1n;
    paint();
    say("Doubled: ×" + fmt(prev) + " → ×" + fmt(scale));
    go(scale);
  }
  function randomBig(bits) {
    var bytes = new Uint8Array(Math.ceil(bits / 8));
    if (window.crypto && crypto.getRandomValues) crypto.getRandomValues(bytes);
    else for (var i = 0; i < bytes.length; i++) bytes[i] = Math.floor(Math.random() * 256);
    var hx = "";
    for (var j = 0; j < bytes.length; j++) hx += bytes[j].toString(16).padStart(2, "0");
    return BigInt("0x" + (hx || "0"));
  }
  function discover() {
    var bits = 16 + Math.floor(Math.random() * 64) + level * 4;
    var id = randomBig(bits);
    if (Math.random() < 0.25) id = -id;
    go(id);
    say("Discovered " + profile(id).name + " · ID " + shortId(id, false));
  }
  function search(raw) {
    raw = raw.replace(/[\s,_]/g, "");
    if (!/^[+-]?(\d+|0x[0-9a-f]+)$/i.test(raw) || raw.length > 20000) {
      say("Enter a whole number, e.g. 42 or -7 or 0xFF. Any size works.");
      return;
    }
    var neg = raw.charAt(0) === "-", body = raw.replace(/^[+-]/, "");
    var id = BigInt(body);
    if (neg) id = -id;
    go(id);
    say("Generated profile for ID " + shortId(id, false));
  }

  $("prev").onclick = function () { step(-1n); };
  $("next").onclick = function () { step(1n); };
  $("mul").onclick = multiply;
  $("dis").onclick = discover;
  form.addEventListener("submit", function (e) { e.preventDefault(); search(q.value); });
  feed.addEventListener("click", function (e) {
    var b = e.target.closest && e.target.closest("button[data-act=echo]");
    if (!b) return;
    var c = b.closest(".card"), target = c._id * scale;
    go(target);
    say("Echo: ID " + shortId(c._id, false) + " × " + fmt(scale) + " → " + shortId(target, false));
  });

  /* ---------- start ---------- */
  var start = null, m = /^#(\d{1,6}):(-?\d+)$/.exec(location.hash);
  if (m) { level = parseInt(m[1], 10); scale = 1n << BigInt(level); start = BigInt(m[2]); }
  paint();
  go(start === null ? scale : start);

  if (window.fetch) {
    fetch("data.txt", { cache: "no-cache" })
      .then(function (r) { return r.ok ? r.text() : ""; })
      .then(function (t) {
        if (t && parseData(t)) { var keep = focus; go(keep); }
      })
      .catch(function () {});
  }
})();
