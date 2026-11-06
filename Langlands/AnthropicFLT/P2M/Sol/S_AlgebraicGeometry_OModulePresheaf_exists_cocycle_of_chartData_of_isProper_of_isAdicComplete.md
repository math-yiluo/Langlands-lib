# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_of_chartData_of_isProper_of_isAdicComplete`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_of_chartData_of_isProper_of_isAdicComplete.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_of_chartData_of_isProper_of_isAdicComplete.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_cocycle_of_chartData_of_isProper_of_isAdicComplete`.

Proof. Helpers: `RedY1.cocycle_of_regimes` shows that a family `w i j` defined by `v i j` for `i < j`, by the
inverse of `v j i` for `i > j` and by the identity for `i = j` satisfies the cocycle condition for all triples once
`v` satisfies it for increasing triples and the inverses are two-sided; `RedY1.cocAux` is an abelian-group identity.

`solution`: `P` is locally noetherian, and `internalHom GE GK` is coherent and quasi-coherent (ported theorem
`isCoherent_internalHom_and_existsUnique_eval_eq`). The ported theorem
`exists_cochain_internalHom_forall_eq_comp_sub_of_chartData` gives the obstruction `2`-cochain `g` of the overlap
isomorphisms `u`; it is a cocycle (ported theorem `d_eq_zero_of_forall_eq_comp_sub_of_chartData`) and a coboundary
modulo every power of `I` (ported theorem `mem_pow_smul_sup_range_d_of_forall_eq_comp_sub_of_chartData`), hence a
coboundary `g = d β` (ported theorem
`mem_range_d_of_d_eq_zero_of_forall_mem_pow_smul_sup_range_d_of_isAdicComplete_of_isProper`, using completeness).
For charts `i < j` put `v = u − ϑ ∘ β_{ij} ∘ θE` on affine `W ⊆ U_i ∩ U_j` (with `pr`, `tr` the `1`- and `2`-simplices
of pairs and triples, their faces `hface0`–`hface2`, and `hkey` the expansion of `g = d β`); these corrected maps
still respect `ϑ`, `θE`, scalars and restriction, are bijective, and satisfy the cocycle condition on increasing
triples. Extending to all pairs by inverses and identities (`cocycle_of_regimes`) gives `u'` with all the claimed
properties.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_of_chartData_of_isProper_of_isAdicComplete.RedY1.cocycle_of_regimes`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_of_chartData_of_isProper_of_isAdicComplete.RedY1.cocAux`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_of_chartData_of_isProper_of_isAdicComplete.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_LinearMap_existsUnique_sub_eq_comp_comp_of_extension` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_cochain_internalHom_forall_eq_comp_sub_of_chartData` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_eq_zero_of_forall_eq_comp_sub_of_chartData` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_mem_pow_smul_sup_range_d_of_forall_eq_comp_sub_of_chartData` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_mem_range_d_of_d_eq_zero_of_forall_mem_pow_smul_sup_range_d_of_isAdicComplete_of_isProper` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafInternalHom` (same contribution).
Other imports: `Mathlib`.
