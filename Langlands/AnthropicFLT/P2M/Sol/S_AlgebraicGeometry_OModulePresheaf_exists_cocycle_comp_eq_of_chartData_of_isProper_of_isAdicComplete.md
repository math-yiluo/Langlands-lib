# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_isProper_of_isAdicComplete`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_isProper_of_isAdicComplete.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_isProper_of_isAdicComplete.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_isProper_of_isAdicComplete`.

Proof (direct). The ported theorem `exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData_of_cocycle`
gives `1`-cochains `t k` of `internalHom GE GK` measuring the disagreement of the chart maps, which are cocycles
modulo `I^(k+1)` and converge. `internalHom GE GK` is coherent and quasi-coherent (ported theorem
`isCoherent_internalHom_and_existsUnique_eval_eq`), so the ported theorem
`exists_d_eq_zero_forall_sub_sub_d_mem_pow_smul_of_isAdicComplete_of_isProper` gives a cocycle `z` and convergent
`0`-cochains `Y k` with `t k − z − d (Y k) ∈ I^(k+1)`. The ported theorem
`exists_cocycle_comp_eq_of_chartData_of_internalHom_cocycle`, applied with `−Y k`, gives the corrected chart maps
and overlap isomorphisms.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_isProper_of_isAdicComplete.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafInternalHom` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData_of_cocycle` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_forall_sub_sub_d_mem_pow_smul_of_isAdicComplete_of_isProper` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_internalHom_cocycle` (same contribution).
Other imports: `Mathlib`.
