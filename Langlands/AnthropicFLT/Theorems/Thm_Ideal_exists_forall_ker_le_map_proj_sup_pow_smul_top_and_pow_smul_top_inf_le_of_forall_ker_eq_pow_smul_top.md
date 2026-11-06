# `Langlands.AnthropicFLT.Theorems.Thm_Ideal_exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_Ideal_exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_Ideal_exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_Ideal_exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top.solution J F P φ hφs hφk π hπs hπk u hu K hK`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `Ideal.exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top`:
let `B` be a noetherian commutative ring with an ideal `J`, and `F n`, `P n` two adic systems of finite
`B`-modules (transition maps `φ n`, `π n` surjective with kernels `J^(n+1) • ⊤`), with compatible maps
`u n : F n → P n` (`π n ∘ u (n+1) = u n ∘ φ n`). Let `K ⊆ ∏ F n` be the submodule of compatible sequences
`x` with `u n (x n) = 0` for all `n` (hypothesis `hK`; the inverse limit of the kernels). Then there is `c`
such that for `k + c ≤ n`: `ker (u n) ≤ proj_n(K) ⊔ J^(k+1) • ⊤`, and
`J^n • ⊤ ⊓ proj_n(K) ≤ J^k • proj_n(K)`, where `proj_n(K)` is the image of `K` in `F n`.

The proof term applies the companion solution theorem
`P2MW.S_Ideal_exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top.solution`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `Ideal.exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.P2M.Sol.S_Ideal_exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top` (same contribution).
Other imports: `Mathlib`.
