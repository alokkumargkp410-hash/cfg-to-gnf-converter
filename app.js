// ──────────────────────────────────────────────
//  EXAMPLES
// ──────────────────────────────────────────────
const EXAMPLES = [
  { text: "S -> AB | a\nA -> aA | a\nB -> bB | b", start: "S" },
  { text: "S -> AB | eps\nA -> aA | eps\nB -> bB | b", start: "S" },
  { text: "S -> A | B | ab\nA -> a | C\nB -> b\nC -> c", start: "S" },
  { text: "S -> aAb | B\nA -> aA | C | eps\nB -> bB | b\nC -> cC | eps", start: "S" }
];

function loadEx(i) {
  document.getElementById('grammar-input').value = EXAMPLES[i].text;
  document.getElementById('start-sym').value = EXAMPLES[i].start;
}

// ──────────────────────────────────────────────
//  PARSING
// ──────────────────────────────────────────────
function parseGrammar(text, startSym) {
  const rules = {};
  const lines = text.trim().split('\n').map(l => l.trim()).filter(l => l && !l.startsWith('//'));
  if (!lines.length) throw new Error("Please enter at least one production rule.");
  for (const line of lines) {
    const arrowIdx = line.indexOf('->');
    if (arrowIdx < 0) throw new Error(`Missing '->' in rule: "${line}"`);
    const lhs = line.slice(0, arrowIdx).trim();
    if (!lhs || !/^[A-Z][A-Z0-9'_]*$/.test(lhs))
      throw new Error(`Invalid variable name: "${lhs}". Variables must begin with uppercase.`);
    const rhsPart = line.slice(arrowIdx + 2);
    const alts = rhsPart.split('|').map(r => r.trim()).filter(r => r.length > 0);
    if (!rules[lhs]) rules[lhs] = new Set();
    for (const alt of alts) {
      const norm = (alt === 'eps' || alt === 'ε' || alt === 'epsilon') ? 'ε' : alt;
      rules[lhs].add(norm);
    }
  }
  const variables = new Set(Object.keys(rules));
  const start = (startSym || 'S').trim();
  if (!variables.has(start)) throw new Error(`Start symbol "${start}" not found. Add a rule for it.`);
  return { rules, variables, start };
}

function cloneRules(r) {
  const o = {};
  for (const k in r) o[k] = new Set([...r[k]]);
  return o;
}

function cloneState(s) {
  return { rules: cloneRules(s.rules), variables: new Set([...s.variables]), start: s.start };
}

// ──────────────────────────────────────────────
//  TOKENIZER
// ──────────────────────────────────────────────
function tokenize(prod, variables) {
  if (prod === 'ε') return ['ε'];
  const tokens = [];
  const varsSorted = [...variables].sort((a, b) => b.length - a.length);
  let i = 0;
  while (i < prod.length) {
    let matched = false;
    for (const v of varsSorted) {
      if (prod.startsWith(v, i)) { tokens.push(v); i += v.length; matched = true; break; }
    }
    if (!matched) { tokens.push(prod[i]); i++; }
  }
  return tokens;
}

function getAllTerminals(rules, variables) {
  const t = new Set();
  for (const prods of Object.values(rules))
    for (const p of prods)
      if (p !== 'ε')
        for (const tok of tokenize(p, variables))
          if (!variables.has(tok)) t.add(tok);
  return t;
}

// ──────────────────────────────────────────────
//  TRANSFORMATIONS
// ──────────────────────────────────────────────
let varCounter = 0;
function freshVar(prefix, vars) {
  let v;
  do { v = prefix + (++varCounter); } while (vars.has(v));
  return v;
}

function step_newStart(state) {
  const { rules, variables, start } = state;
  const newStart = start + '0';
  varCounter = 0;
  const r = cloneRules(rules);
  const vars = new Set([...variables]);
  r[newStart] = new Set([start]);
  vars.add(newStart);
  const newVars = [newStart];
  return {
    rules: r, variables: vars, start: newStart,
    explanation: {
      summary: `A fresh start symbol <em>${newStart}</em> is introduced with a single unit production <em>${newStart} → ${start}</em>. This guarantees the start symbol never appears on the right-hand side of any rule — a prerequisite for both CNF and GNF conversions.`,
      formal: [
        { lhs: newStart, rhs: `${start}`, note: "new production" }
      ]
    },
    changes: { added: [newStart], removed: [] }
  };
}

function step_removeUseless(state) {
  const { rules, variables, start } = state;
  const r = cloneRules(rules);
  const vars = new Set([...variables]);

  // Generating
  const generating = new Set();
  let changed = true;
  while (changed) {
    changed = false;
    for (const v of vars) {
      if (generating.has(v)) continue;
      for (const prod of (r[v] || [])) {
        if (prod === 'ε') { generating.add(v); changed = true; break; }
        const toks = tokenize(prod, vars);
        if (toks.every(t => !vars.has(t) || generating.has(t))) { generating.add(v); changed = true; break; }
      }
    }
  }
  const nonGen = [...vars].filter(v => !generating.has(v));
  for (const v of nonGen) { delete r[v]; vars.delete(v); }
  for (const v of [...vars]) {
    r[v] = new Set([...r[v]].filter(prod => {
      if (prod === 'ε') return true;
      return tokenize(prod, variables).every(t => !variables.has(t) || generating.has(t));
    }));
    if (!r[v].size) { delete r[v]; vars.delete(v); }
  }

  // Reachable
  const reachable = new Set([start]);
  const queue = [start];
  while (queue.length) {
    const v = queue.shift();
    for (const prod of (r[v] || [])) {
      if (prod === 'ε') continue;
      for (const t of tokenize(prod, vars))
        if (vars.has(t) && !reachable.has(t)) { reachable.add(t); queue.push(t); }
    }
  }
  const unreachable = [...vars].filter(v => !reachable.has(v));
  for (const v of unreachable) { delete r[v]; vars.delete(v); }

  return {
    rules: r, variables: vars, start,
    explanation: {
      summary: `<strong>Non-generating variables</strong> (those that cannot derive any terminal string): <em>${nonGen.join(', ') || 'none'}</em>. <strong>Unreachable variables</strong> (not derivable from start): <em>${unreachable.join(', ') || 'none'}</em>. Both classes are useless and safely removed along with all rules containing them.`,
      formal: [
        { lhs: "Non-generating", rhs: nonGen.join(', ') || 'none', note: "" },
        { lhs: "Unreachable", rhs: unreachable.join(', ') || 'none', note: "" }
      ]
    },
    changes: { removed: [...nonGen, ...unreachable], added: [] }
  };
}

function step_removeEpsilon(state) {
  const { rules, variables, start } = state;
  const r = cloneRules(rules);
  const vars = new Set([...variables]);

  // Find nullable
  const nullable = new Set();
  for (const v of vars) if (r[v] && r[v].has('ε')) nullable.add(v);
  let changed = true;
  while (changed) {
    changed = false;
    for (const v of vars) {
      if (nullable.has(v)) continue;
      for (const prod of (r[v] || [])) {
        const toks = tokenize(prod, vars);
        if (toks.every(t => nullable.has(t))) { nullable.add(v); changed = true; break; }
      }
    }
  }

  // Expand combinations
  for (const v of vars) {
    const expanded = new Set();
    for (const prod of (r[v] || [])) {
      if (prod === 'ε') continue;
      const toks = tokenize(prod, vars);
      const nullIdx = toks.map((t, i) => nullable.has(t) ? i : -1).filter(x => x >= 0);
      for (let mask = 0; mask < (1 << nullIdx.length); mask++) {
        const skip = new Set(nullIdx.filter((_, j) => mask & (1 << j)));
        const newProd = toks.filter((_, i) => !skip.has(i)).join('');
        if (newProd) expanded.add(newProd);
      }
      expanded.add(prod);
    }
    r[v] = expanded;
  }
  for (const v of vars) if (v !== start) r[v].delete('ε');

  const nullStr = [...nullable].join(', ') || 'none';
  return {
    rules: r, variables: vars, start,
    explanation: {
      summary: `Nullable variables (can derive ε): <em>${nullStr}</em>. For each production containing a nullable symbol, we generate all subsets (with/without each nullable occurrence), then remove ε-productions from all non-start variables. If the start is nullable, it retains its ε-rule.`,
      formal: [
        { lhs: "Nullable set", rhs: `{ ${nullStr} }`, note: "" },
        { lhs: "Rule", rhs: "A → αBβ where B ∈ Nullable ⇒ add A → αβ", note: "" }
      ]
    },
    changes: { added: [], removed: [] }
  };
}

function step_removeUnit(state) {
  const { rules, variables, start } = state;
  const r = cloneRules(rules);
  const vars = new Set([...variables]);

  for (const v of vars) {
    const closure = new Set([v]);
    const queue = [v];
    while (queue.length) {
      const cur = queue.shift();
      for (const prod of (r[cur] || [])) {
        const toks = tokenize(prod, vars);
        if (toks.length === 1 && vars.has(toks[0]) && !closure.has(toks[0])) {
          closure.add(toks[0]); queue.push(toks[0]);
        }
      }
    }
    const nonUnit = new Set();
    for (const u of closure)
      for (const prod of (r[u] || [])) {
        const toks = tokenize(prod, vars);
        if (!(toks.length === 1 && vars.has(toks[0]))) nonUnit.add(prod);
      }
    r[v] = nonUnit;
  }

  return {
    rules: r, variables: vars, start,
    explanation: {
      summary: `Unit productions have the form <em>A → B</em> (single variable). For each variable A, we compute its <strong>unit closure</strong> — all variables reachable through chains of unit productions — and replace A's unit productions with the non-unit productions of all closure members.`,
      formal: [
        { lhs: "Unit(A)", rhs: "{ B : A ⟹* B via unit rules }", note: "" },
        { lhs: "New rules", rhs: "A → α for all B ∈ Unit(A), B → α not a unit rule", note: "" }
      ]
    },
    changes: { added: [], removed: [] }
  };
}

function step_toCNF(state) {
  const { rules, variables, start } = state;
  const r = cloneRules(rules);
  const vars = new Set([...variables]);
  const termMap = {};
  const newTermVars = [];

  // Replace terminals in long/mixed productions
  for (const v of [...vars]) {
    const newP = new Set();
    for (const prod of [...r[v]]) {
      const toks = tokenize(prod, vars);
      if (toks.length === 1) { newP.add(prod); continue; }
      const mapped = toks.map(t => {
        if (vars.has(t)) return t;
        if (!termMap[t]) {
          const nv = freshVar('T', vars);
          termMap[t] = nv;
          vars.add(nv);
          r[nv] = new Set([t]);
          newTermVars.push(nv);
        }
        return termMap[t];
      });
      newP.add(mapped.join(''));
    }
    r[v] = newP;
  }

  // Break into binary
  const newChainVars = [];
  for (const v of [...vars]) {
    if (newTermVars.includes(v)) continue;
    const newP = new Set();
    for (const prod of [...r[v]]) {
      let toks = tokenize(prod, vars);
      if (toks.length <= 2) { newP.add(prod); continue; }
      let cur = null;
      let first = true;
      while (toks.length > 2) {
        const nv = freshVar('C', vars);
        vars.add(nv); r[nv] = new Set(); newChainVars.push(nv);
        if (first) { newP.add(toks[0] + nv); first = false; cur = nv; }
        else { r[cur].add(toks[0] + nv); cur = nv; }
        toks = toks.slice(1);
      }
      if (cur) r[cur].add(toks.join(''));
      else newP.add(toks.join(''));
    }
    r[v] = newP;
  }

  return {
    rules: r, variables: vars, start,
    explanation: {
      summary: `<strong>CNF requires:</strong> every production is either <em>A → BC</em> (two variables) or <em>A → a</em> (one terminal). Step 1 — terminals in mixed/long productions are abstracted into new unit rules <em>Tₙ → a</em>. Step 2 — any production with 3+ symbols is split into a right-branching chain of binary productions using new variables <em>Cₙ</em>.`,
      formal: [
        { lhs: "Term vars", rhs: newTermVars.join(', ') || 'none', note: "Tₙ → a" },
        { lhs: "Chain vars", rhs: newChainVars.join(', ') || 'none', note: "binarization" },
        { lhs: "CNF form", rhs: "A → BC  |  A → a", note: "" }
      ]
    },
    changes: { added: [...newTermVars, ...newChainVars], removed: [] }
  };
}

function step_toGNF(state) {
  const r = cloneRules(state.rules);
  const vars = new Set([...state.variables]);
  const { start } = state;
  const newVars = [];

  const orderedVars = [start, ...[...vars].filter(v => v !== start).sort()];

  // Phase 1: Eliminate left recursion
  for (let i = 0; i < orderedVars.length; i++) {
    const Ai = orderedVars[i];
    if (!r[Ai]) r[Ai] = new Set();

    for (let j = 0; j < i; j++) {
      const Aj = orderedVars[j];
      const toAdd = new Set(), toRem = new Set();
      for (const prod of r[Ai]) {
        const toks = tokenize(prod, vars);
        if (toks[0] === Aj) {
          toRem.add(prod);
          for (const sp of (r[Aj] || [])) {
            const st = tokenize(sp, vars);
            toAdd.add([...st, ...toks.slice(1)].join(''));
          }
        }
      }
      toRem.forEach(p => r[Ai].delete(p));
      toAdd.forEach(p => r[Ai].add(p));
    }

    // Immediate left recursion
    const rec = [], nonRec = [];
    for (const prod of r[Ai]) {
      const toks = tokenize(prod, vars);
      (toks[0] === Ai ? rec : nonRec).push(toks);
    }
    if (rec.length) {
      const Bi = freshVar('R', vars);
      vars.add(Bi); r[Bi] = new Set(); newVars.push(Bi);
      r[Ai] = new Set();
      for (const beta of nonRec) r[Ai].add([...beta, Bi].join(''));
      for (const alpha of rec) {
        r[Bi].add([...alpha, Bi].join(''));
        r[Bi].add(alpha.join(''));
      }
      orderedVars.splice(i + 1, 0, Bi);
    }
  }

  // Phase 2: Substitute until all start with terminal
  for (let iter = 0; iter < 80; iter++) {
    let changed = false;
    for (const v of [...vars]) {
      const newP = new Set();
      for (const prod of [...(r[v] || [])]) {
        const toks = tokenize(prod, vars);
        if (!toks.length || !vars.has(toks[0])) { newP.add(prod); continue; }
        const fv = toks[0];
        for (const sp of (r[fv] || [])) {
          const st = tokenize(sp, vars);
          const np = [...st, ...toks.slice(1)].join('');
          newP.add(np);
          if (vars.has(st[0])) changed = true;
        }
      }
      r[v] = newP;
    }
    if (!changed) break;
  }

  return {
    rules: r, variables: vars, start,
    explanation: {
      summary: `<strong>GNF requires:</strong> every production starts with a terminal: <em>A → aα</em> where α ∈ V*. Phase 1 orders variables and eliminates left recursion (direct and indirect) using new tail variables <em>Rₙ</em>. Phase 2 repeatedly substitutes leading variables until every production begins with a terminal symbol.`,
      formal: [
        { lhs: "New vars", rhs: newVars.join(', ') || 'none', note: "left recursion removal" },
        { lhs: "GNF form", rhs: "A → a α  (a ∈ Σ, α ∈ V*)", note: "" },
        { lhs: "Property", rhs: "Enables O(n³) CYK & LL parsers", note: "" }
      ]
    },
    changes: { added: newVars, removed: [] }
  };
}

// ──────────────────────────────────────────────
//  RENDERING
// ──────────────────────────────────────────────
function renderRHS(prod, vars) {
  if (prod === 'ε') return `<span class="sym-eps">ε</span>`;
  const toks = tokenize(prod, vars);
  return toks.map(t => {
    if (t === 'ε') return `<span class="sym-eps">ε</span>`;
    if (vars.has(t)) return `<span class="sym-var">${t}</span>`;
    return `<span class="sym-term">${t}</span>`;
  }).join('');
}

function renderGrammar(rules, variables, start, highlightNew = []) {
  const sortedVars = [start, ...[...variables].filter(v => v !== start).sort()];
  return sortedVars.filter(v => rules[v]).map(v => {
    const isNew = highlightNew.includes(v);
    const prods = [...rules[v]];
    const alts = prods.map(p => `<span class="rhs-alt">${renderRHS(p, variables)}</span>`);
    const sep = `<span class="rhs-sep">|</span>`;
    return `
      <div class="grammar-rule-row${isNew ? ' new-rule' : ''}">
        ${isNew ? '<div class="changed-indicator"></div>' : ''}
        <div class="rule-lhs-col">${v}</div>
        <div class="rule-arrow-col">→</div>
        <div class="rule-rhs-col">${alts.join(sep)}</div>
      </div>`;
  }).join('');
}

function renderMeta(rules, variables) {
  const terms = getAllTerminals(rules, variables);
  const prodCount = Object.values(rules).reduce((s, p) => s + p.size, 0);
  return `
    <div class="grammar-meta">
      <div class="meta-chip">Variables: <span class="chip-val">${[...variables].sort().join(', ')}</span></div>
      <div class="meta-chip">Terminals: <span class="chip-val">${[...terms].sort().join(', ') || '—'}</span></div>
      <div class="meta-chip">Productions: <span class="chip-val">${prodCount}</span></div>
      <div class="meta-chip">Start: <span class="chip-val">${[...variables][0]}</span></div>
    </div>`;
}

const STEP_DEFS = [
  { id: 0, title: "Original Grammar", sub: "Input CFG as entered", icon: "∑", cls: "icon-default", tag: null, tagcls: "" },
  { id: 1, title: "New Start Symbol", sub: "Isolate start from RHS", icon: "S₀", cls: "icon-default", tag: null, tagcls: "" },
  { id: 2, title: "Remove Useless Symbols", sub: "Non-generating & unreachable", icon: "✕", cls: "icon-default", tag: null, tagcls: "" },
  { id: 3, title: "Eliminate ε-Productions", sub: "Null / empty string rules", icon: "ε", cls: "icon-default", tag: null, tagcls: "" },
  { id: 4, title: "Remove Unit Productions", sub: "Single-variable chains", icon: "↺", cls: "icon-default", tag: null, tagcls: "" },
  { id: 5, title: "Chomsky Normal Form", sub: "A → BC or A → a only", icon: "CNF", cls: "icon-cnf", tag: "CNF", tagcls: "tag-cnf", cardcls: "cnf-card" },
  { id: 6, title: "Greibach Normal Form", sub: "A → aα, terminal-first", icon: "GNF", cls: "icon-gnf", tag: "GNF", tagcls: "tag-gnf", cardcls: "gnf-card" }
];

// ──────────────────────────────────────────────
//  MAIN CONVERSION
// ──────────────────────────────────────────────
function runConversion() {
  const text = document.getElementById('grammar-input').value.trim();
  const startSym = document.getElementById('start-sym').value.trim() || 'S';
  const errBox = document.getElementById('error-box');
  errBox.innerHTML = '';

  if (!text) {
    errBox.innerHTML = `<div class="error-msg">Please enter a grammar before converting.</div>`; return;
  }

  let g;
  try { g = parseGrammar(text, startSym); }
  catch(e) { errBox.innerHTML = `<div class="error-msg">${e.message}</div>`; return; }

  varCounter = 0;
  const steps = [];

  // Step 0: Original
  steps.push({ def: STEP_DEFS[0], state: cloneState(g), result: { explanation: { summary: "The original grammar as entered. Variables are uppercase, terminals are lowercase. This is our starting point — we will systematically transform this CFG without changing the language it generates (except possibly for ε).", formal: [] }, changes: { added: [], removed: [] } } });

  // Step 1
  const s1 = step_newStart(cloneState(g));
  steps.push({ def: STEP_DEFS[1], state: { rules: s1.rules, variables: s1.variables, start: s1.start }, result: s1 });

  // Step 2
  const s2r = step_removeUseless({ rules: s1.rules, variables: s1.variables, start: s1.start });
  const s2 = { rules: s2r.rules, variables: s2r.variables, start: s2r.start };
  steps.push({ def: STEP_DEFS[2], state: cloneState(s2), result: s2r });

  // Step 3
  const s3r = step_removeEpsilon(cloneState(s2));
  const s3 = { rules: s3r.rules, variables: s3r.variables, start: s3r.start };
  steps.push({ def: STEP_DEFS[3], state: cloneState(s3), result: s3r });

  // Step 4
  const s4r = step_removeUnit(cloneState(s3));
  const s4 = { rules: s4r.rules, variables: s4r.variables, start: s4r.start };
  steps.push({ def: STEP_DEFS[4], state: cloneState(s4), result: s4r });

  // Step 5 CNF
  const s5r = step_toCNF(cloneState(s4));
  const s5 = { rules: s5r.rules, variables: s5r.variables, start: s5r.start };
  steps.push({ def: STEP_DEFS[5], state: cloneState(s5), result: s5r });

  // Step 6 GNF (from CNF state)
  const s6r = step_toGNF(cloneState(s5));
  const s6 = { rules: s6r.rules, variables: s6r.variables, start: s6r.start };
  steps.push({ def: STEP_DEFS[6], state: cloneState(s6), result: s6r });

  renderResults(steps);
}

function renderResults(steps) {
  // Build nav
  const navHTML = steps.map((s, i) => `
    <div class="nav-item${i === 5 ? ' cnf-step' : i === 6 ? ' gnf-step' : ''}" onclick="scrollToStep(${i})">
      <div class="nav-num">${i}</div>
      <div class="nav-label">
        <strong>${s.def.title}</strong>
        ${s.def.sub}
      </div>
    </div>`).join('');

  document.getElementById('step-nav').innerHTML = navHTML;
  document.getElementById('nav-section').style.display = 'block';

  // Build cards
  const progressHTML = `<div class="progress-bar"><div class="progress-fill" style="width:100%"></div></div>`;

  const cardsHTML = steps.map((s, i) => {
    const { def, state, result } = s;
    const { rules, variables, start } = state;
    const expl = result.explanation;
    const changes = result.changes || { added: [], removed: [] };
    const prodCount = Object.values(rules).reduce((c, p) => c + p.size, 0);

    const formalHTML = expl.formal && expl.formal.length ? `
      <div class="expl-rules-box">
        <div class="expl-rules-title">Formal definition</div>
        ${expl.formal.map(f => `
          <div class="formal-rule">
            <span class="formal-lhs">${f.lhs}</span>
            <span class="formal-arrow">:</span>
            <span class="formal-rhs">${f.rhs}</span>
            ${f.note ? `<span style="color:var(--text3);font-size:11px;">[${f.note}]</span>` : ''}
          </div>`).join('')}
      </div>` : '';

    const summaryHTML = `
      <div class="step-summary">
        <div class="summary-item">Variables: <span class="s-val">${variables.size}</span></div>
        <div class="summary-item">Productions: <span class="s-val">${prodCount}</span></div>
        ${changes.added.length ? `<div class="summary-item">Added: <span class="s-val s-delta-pos">+${changes.added.join(', ')}</span></div>` : ''}
        ${changes.removed.length ? `<div class="summary-item">Removed: <span class="s-val s-delta-neg">−${changes.removed.join(', ')}</span></div>` : ''}
        <div class="summary-item" style="margin-left:auto;">Start: <span class="s-val">${start}</span></div>
      </div>`;

    const isOpen = i === 0 || i === 5 || i === 6;

    return `
      <div class="step-card ${def.cardcls || ''}" id="step-card-${i}">
        <div class="step-head" onclick="toggleCard(${i})">
          <div class="step-icon ${def.cls}">${def.icon}</div>
          <div class="step-head-info">
            <div class="step-head-title">
              <span style="color:var(--text3);font-size:13px;margin-right:8px;">${i}.</span>${def.title}
            </div>
            <div class="step-head-sub">${def.sub}</div>
          </div>
          ${def.tag ? `<span class="step-tag ${def.tagcls}">${def.tag}</span>` : ''}
          <span class="chevron${isOpen ? ' open' : ''}" id="chev-${i}">▶</span>
        </div>
        <div class="step-body${isOpen ? ' open' : ''}" id="body-${i}">
          <div class="explanation">
            <div class="expl-text">${expl.summary}</div>
            ${formalHTML}
          </div>
          <div class="grammar-section">
            ${renderMeta(rules, variables)}
            <div class="grammar-rules">
              ${renderGrammar(rules, variables, start, changes.added)}
            </div>
          </div>
          ${summaryHTML}
        </div>
      </div>`;
  }).join('');

  document.getElementById('right-panel').innerHTML = progressHTML + `<div class="steps-view">${cardsHTML}</div>`;
}

function toggleCard(i) {
  const body = document.getElementById(`body-${i}`);
  const chev = document.getElementById(`chev-${i}`);
  body.classList.toggle('open');
  chev.classList.toggle('open');
}

function scrollToStep(i) {
  const el = document.getElementById(`step-card-${i}`);
  if (el) { el.scrollIntoView({ behavior: 'smooth', block: 'start' }); }
}

function clearAll() {
  document.getElementById('grammar-input').value = '';
  document.getElementById('start-sym').value = 'S';
  document.getElementById('error-box').innerHTML = '';
  document.getElementById('nav-section').style.display = 'none';
  document.getElementById('right-panel').innerHTML = `
    <div class="welcome-screen">
      <div class="welcome-icon">⊢</div>
      <div class="welcome-title">CFG Normal Form Converter</div>
      <div class="welcome-sub">Enter a Context-Free Grammar and watch it transform step-by-step into both Chomsky Normal Form and Greibach Normal Form with detailed explanations at every stage.</div>
      <div class="welcome-steps">
        <span class="welcome-step-pill">① Remove useless symbols</span>
        <span class="welcome-step-pill">② Eliminate ε-productions</span>
        <span class="welcome-step-pill">③ Remove unit productions</span>
        <span class="welcome-step-pill">④ Chomsky Normal Form</span>
        <span class="welcome-step-pill">⑤ Greibach Normal Form</span>
      </div>
    </div>`;
}

// Load first example on start
loadEx(0);
