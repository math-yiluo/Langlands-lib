# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_forall_sub_sub_d_mem_pow_smul_of_isAdicComplete_of_isProper`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_forall_sub_sub_d_mem_pow_smul_of_isAdicComplete_of_isProper.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_forall_sub_sub_d_mem_pow_smul_of_isAdicComplete_of_isProper.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_forall_sub_sub_d_mem_pow_smul_of_isAdicComplete_of_isProper`.

Proof. Helpers (`D1sAux`): `env c` is the monotone envelope of a sequence `c` (`le_env`, `env_mono`). `solution`:
the `t n` are Cauchy (`htele`). In degree `i`, approximate cocycles are close to cocycles (`hML`: the ported theorem
`exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper` for `i = 0` and
`exists_d_succ_eq_zero_sub_mem_pow_of_d_succ_mem_pow_of_isProper` otherwise, with constants `c n`). The ported
theorem `exists_d_eq_zero_forall_sub_mem_pow_smul_sup_range_d_of_isAdicComplete_of_isProper` gives a cocycle `a` and
`y n` with `t n − a − d (y n) ∈ I^(n+1)`. Along the reindexing `m n ≥ n + 1 + c (n+1)` (`env`), the differences
`y (m (n+1)) − y (m n)` have coboundary in `I^(n+1+c(n+1))`, so they differ from cocycles `z n` by elements of
`I^(n+1)`; subtracting the partial sums of the `z n` (which do not change `d`) gives `Y n` with
`Y (n+1) − Y n ∈ I^(n+1)` and `t n − a − d (Y n) ∈ I^(n+1)`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_forall_sub_sub_d_mem_pow_smul_of_isAdicComplete_of_isProper.D1sAux.env`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_forall_sub_sub_d_mem_pow_smul_of_isAdicComplete_of_isProper.D1sAux.le_env`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_forall_sub_sub_d_mem_pow_smul_of_isAdicComplete_of_isProper.D1sAux.env_mono`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_forall_sub_sub_d_mem_pow_smul_of_isAdicComplete_of_isProper.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_forall_sub_mem_pow_smul_sup_range_d_of_isAdicComplete_of_isProper` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_zero_sub_mem_pow_of_d_succ_mem_pow_of_isProper` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper` (same contribution).
Other imports: `Mathlib`.
