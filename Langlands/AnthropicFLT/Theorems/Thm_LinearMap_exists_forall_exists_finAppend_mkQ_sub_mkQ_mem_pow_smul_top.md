# `Langlands.AnthropicFLT.Theorems.Thm_LinearMap_exists_forall_exists_finAppend_mkQ_sub_mkQ_mem_pow_smul_top`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_LinearMap_exists_forall_exists_finAppend_mkQ_sub_mkQ_mem_pow_smul_top.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_LinearMap_exists_forall_exists_finAppend_mkQ_sub_mkQ_mem_pow_smul_top.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_LinearMap_exists_forall_exists_finAppend_mkQ_sub_mkQ_mem_pow_smul_top.solution J F E ε ψE lam hlamr hlami p₁ hp₁ p₂ hp₂ P hP`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `LinearMap.exists_forall_exists_finAppend_mkQ_sub_mkQ_mem_pow_smul_top`: let `B` be a noetherian
commutative ring, `J` an ideal, `GK` a finite `B`-module, and `ε k : F k → E k`, `ψE k : GE → E k`,
`lam k : GK → F k` linear maps with `range (lam k) = ker (ε k)` and `ker (lam (k+c₀)) ⊆ J^(k+1) GK` for some `c₀`. Let
`p₁ : B^{r₁} → GE`, `p₂ : B^{r₂} → GE` be surjections and `P : B^(r₁+r₂) → GE` their sum
(`P (append v w) = p₁ v + p₂ w`). Then there is `c` such that for every `n`, all lifts `ℓ_i : B^{r_i} → F (n+c)` of
`ψE ∘ p_i` along `ε` and all `δ_i : ker p_i → GK` with `lam ∘ δ_i = ℓ_i` on `ker p_i`, there are
`δ₁', δ₂' : ker P → GK` extending `δ₁` on `ker p₁ × 0` and `δ₂` on `0 × ker p₂` whose classes in the presentation model
`Hom(ker P, GK) / (maps extending to B^(r₁+r₂))` differ by an element of `J^(n+1) • (that quotient)`. (Comparison of
the obstruction classes computed from two presentations, used on overlaps of charts.)

The proof term applies the companion solution theorem
`P2MW.S_LinearMap_exists_forall_exists_finAppend_mkQ_sub_mkQ_mem_pow_smul_top.solution`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `LinearMap.exists_forall_exists_finAppend_mkQ_sub_mkQ_mem_pow_smul_top`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.P2M.Sol.S_LinearMap_exists_forall_exists_finAppend_mkQ_sub_mkQ_mem_pow_smul_top` (same contribution).
Other imports: `Mathlib`.
