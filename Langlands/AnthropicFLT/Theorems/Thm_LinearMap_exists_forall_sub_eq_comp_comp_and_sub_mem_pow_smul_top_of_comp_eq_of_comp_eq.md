# `Langlands.AnthropicFLT.Theorems.Thm_LinearMap_exists_forall_sub_eq_comp_comp_and_sub_mem_pow_smul_top_of_comp_eq_of_comp_eq`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_LinearMap_exists_forall_sub_eq_comp_comp_and_sub_mem_pow_smul_top_of_comp_eq_of_comp_eq.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_LinearMap_exists_forall_sub_eq_comp_comp_and_sub_mem_pow_smul_top_of_comp_eq_of_comp_eq.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_LinearMap_exists_forall_sub_eq_comp_comp_and_sub_mem_pow_smul_top_of_comp_eq_of_comp_eq.solution I ϑ θE hex hθE F φ hF lam hlamc c hlami E ε hlamr θ θ' hθc hθ'c hθϑ hθ'ϑ hθε`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `LinearMap.exists_forall_sub_eq_comp_comp_and_sub_mem_pow_smul_top_of_comp_eq_of_comp_eq`: let `B` be a
noetherian commutative ring, `I` an ideal, `GK, GE` finite `B`-modules, `0 → GK →ϑ M →θE GE → 0` exact (with
`range ϑ = ker θE`, `θE` surjective), `F k` modules killed by `I^(k+1)` with maps `φ k : F (k+1) → F k`, and
`lam k : GK → F k` compatible with `φ` with `ker (lam (k+c)) ⊆ I^(k+1) GK` for some `c`; let `ε k : F k → E k` with
`range (lam k) = ker (ε k)`. If `θ, θ' : M → F k` are two compatible families both extending `lam k` along `ϑ` and
agreeing after `ε k`, then there are `g k : GE → GK` with `g (k+1) − g k ∈ I^(k+1) • Hom(GE, GK)` and
`θ' k − θ k = lam k ∘ g k ∘ θE`. (Two compatible maps from an extension to the system `F` differ by an
`I`-adically convergent sequence of homomorphisms `GE → GK`.)

The proof term applies the companion solution theorem
`P2MW.S_LinearMap_exists_forall_sub_eq_comp_comp_and_sub_mem_pow_smul_top_of_comp_eq_of_comp_eq.solution`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `LinearMap.exists_forall_sub_eq_comp_comp_and_sub_mem_pow_smul_top_of_comp_eq_of_comp_eq`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.P2M.Sol.S_LinearMap_exists_forall_sub_eq_comp_comp_and_sub_mem_pow_smul_top_of_comp_eq_of_comp_eq` (same contribution).
Other imports: `Mathlib`.
