# `Langlands.AnthropicFLT.Theorems.Thm_LinearMap_exists_forall_comp_eq_comp_subtype_eq_of_forall_sub_mem_pow_smul_sup_range`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_LinearMap_exists_forall_comp_eq_comp_subtype_eq_of_forall_sub_mem_pow_smul_sup_range.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_LinearMap_exists_forall_comp_eq_comp_subtype_eq_of_forall_sub_mem_pow_smul_sup_range.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_LinearMap_exists_forall_comp_eq_comp_subtype_eq_of_forall_sub_mem_pow_smul_sup_range.solution J p hp F E φ hφs hφk ε ψE lam hlamc hlamr ℓ hℓε hℓφ δs hδs hδsc δ hδ`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `LinearMap.exists_forall_comp_eq_comp_subtype_eq_of_forall_sub_mem_pow_smul_sup_range`: let `B` be a
noetherian commutative ring, `J` an ideal, `p : B^r → GE` a surjection, `GK` a finite module, `F` a `J`-adic system
(transition maps `φ k` surjective with kernels `J^(k+1) F_{k+1}`), `ε k : F k → E k`, `ψE k : GE → E k`, and
`lam k : GK → F k` compatible with `φ` with `range (lam k) = ker (ε k)`. Let `ℓ n : B^r → F n` be compatible lifts of
`ψE n ∘ p` along `ε n`, and `δs n : ker p → GK` with `lam n ∘ δs n = ℓ n` on `ker p` and
`δs (n+1) − δs n ∈ J^(n+1) • Hom(ker p, GK)`. If `δ : ker p → GK` satisfies
`δ − δs n ∈ J^(n+1) • Hom(ker p, GK) + (maps extending to B^r)` for every `n`, then there are compatible lifts
`ℓ' k : B^r → F k` (`φ k ∘ ℓ' (k+1) = ℓ' k`, `ε k ∘ ℓ' k = ψE k ∘ p`) whose restrictions to `ker p` are exactly
`lam k ∘ δ`. (A limit class `δ` of the obstruction classes can be realized by a coherent choice of lifts.)

The proof term applies the companion solution theorem
`P2MW.S_LinearMap_exists_forall_comp_eq_comp_subtype_eq_of_forall_sub_mem_pow_smul_sup_range.solution`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `LinearMap.exists_forall_comp_eq_comp_subtype_eq_of_forall_sub_mem_pow_smul_sup_range`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.P2M.Sol.S_LinearMap_exists_forall_comp_eq_comp_subtype_eq_of_forall_sub_mem_pow_smul_sup_range` (same contribution).
Other imports: `Mathlib`.
