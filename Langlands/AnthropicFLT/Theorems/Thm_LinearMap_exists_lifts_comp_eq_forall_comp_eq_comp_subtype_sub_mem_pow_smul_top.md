# `Langlands.AnthropicFLT.Theorems.Thm_LinearMap_exists_lifts_comp_eq_forall_comp_eq_comp_subtype_sub_mem_pow_smul_top`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_LinearMap_exists_lifts_comp_eq_forall_comp_eq_comp_subtype_sub_mem_pow_smul_top.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_LinearMap_exists_lifts_comp_eq_forall_comp_eq_comp_subtype_sub_mem_pow_smul_top.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_LinearMap_exists_lifts_comp_eq_forall_comp_eq_comp_subtype_sub_mem_pow_smul_top.solution J p F E φ hφs hφk τ hτk ε hεs hεc ψE hψEc lam hlamc hlamr hlami`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `LinearMap.exists_lifts_comp_eq_forall_comp_eq_comp_subtype_sub_mem_pow_smul_top`: let `B` be a
noetherian commutative ring, `J` an ideal, `p : B^r → GE` a linear map and `GK` a finite `B`-module. Let
`F, E : ℕ → B`-modules form `J`-adic systems (transition maps `φ k` surjective with kernel `J^(k+1) F_{k+1}`, and
`τ k` with kernel `J^(k+1) E_{k+1}`) with compatible surjections `ε k : F k → E k`; let `ψE k : GE → E k` and
`lam k : GK → F k` be compatible with the transition maps, with `range (lam k) = ker (ε k)` and
`ker (lam (k+c)) ⊆ J^(k+1) GK` for some `c`. Then there are compatible lifts `ℓ n : B^r → F n` of `ψE n ∘ p` along
`ε n` (`ε n ∘ ℓ n = ψE n ∘ p`, `φ n ∘ ℓ (n+1) = ℓ n`) and maps `δs n : ker p → GK` with
`lam n ∘ δs n = ℓ n` on `ker p` and `δs (n+1) − δs n ∈ J^(n+1) • Hom(ker p, GK)`. (The obstruction data of the
extension `0 → GK → ? → GE → 0` form a `J`-adically convergent sequence.)

The proof term applies the companion solution theorem
`P2MW.S_LinearMap_exists_lifts_comp_eq_forall_comp_eq_comp_subtype_sub_mem_pow_smul_top.solution`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `LinearMap.exists_lifts_comp_eq_forall_comp_eq_comp_subtype_sub_mem_pow_smul_top`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.P2M.Sol.S_LinearMap_exists_lifts_comp_eq_forall_comp_eq_comp_subtype_sub_mem_pow_smul_top` (same contribution).
Other imports: `Mathlib`.
