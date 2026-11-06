# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_basisData_of_chartData_of_cocycle_of_comp_eq`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_basisData_of_chartData_of_cocycle_of_comp_eq.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Each FLT command `p2m_reactivate "N₁ N₂ …"` (from `P2M.Util`; it re-activates the scoped declarations of the namespaces) is replaced by `open scoped N₁ N₂ …`.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_basisData_of_chartData_of_cocycle_of_comp_eq.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_basisData_of_chartData_of_cocycle_of_comp_eq`.

Proof (namespace `GlueY3Sol`): turning glued chart data into data on a basis. `B K` is the set of affine opens
contained in some chart; it is closed under shrinking and covers `P` (`B`, `hdown`, `hcov`). Each `U ∈ B K` gets a
chosen chart `idx K U` containing it (`le_idx`, `toChart`, `toChart'`), and `N K M U = M (idx U) U` (with its
instances `instN1`, `instN2`, `instNΓ`). The restriction `Nres` from `U` to `U' ⊆ U` restricts inside the chart of
`U` and then moves to the chart of `U'` with the overlap isomorphism (`Nres_apply`).

`solution`: `u i i = id` (from the cocycle condition and bijectivity). The data are `B K`, `N`, `Nres`, and `ϑ`,
`θE`, `θF` taken in the chosen chart. Semilinearity of `Nres` comes from `res_smul` and `hus`; `Nres` is unital
(`res_refl`, `u i i = id`) and transitive (`res_comp`, `hun` and the cocycle condition); the localization
conditions `hqc` transfer through the bijective `u`; finiteness, exactness and the compatibilities with `ϑ`, `θE`,
`θF`, `φ`, `lam`, `ε`, `ψE` follow from the chart data and the compatibility of `u` with `ϑ`, `θE` and `θF`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_basisData_of_chartData_of_cocycle_of_comp_eq.GlueY3Sol.B`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_basisData_of_chartData_of_cocycle_of_comp_eq.GlueY3Sol.hdown`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_basisData_of_chartData_of_cocycle_of_comp_eq.GlueY3Sol.hcov`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_basisData_of_chartData_of_cocycle_of_comp_eq.GlueY3Sol.idx`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_basisData_of_chartData_of_cocycle_of_comp_eq.GlueY3Sol.le_idx`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_basisData_of_chartData_of_cocycle_of_comp_eq.GlueY3Sol.toChart`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_basisData_of_chartData_of_cocycle_of_comp_eq.GlueY3Sol.toChart'`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_basisData_of_chartData_of_cocycle_of_comp_eq.GlueY3Sol.N`
- instance `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_basisData_of_chartData_of_cocycle_of_comp_eq.GlueY3Sol.instN1`
- instance `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_basisData_of_chartData_of_cocycle_of_comp_eq.GlueY3Sol.instN2`
- instance `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_basisData_of_chartData_of_cocycle_of_comp_eq.GlueY3Sol.instNΓ`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_basisData_of_chartData_of_cocycle_of_comp_eq.GlueY3Sol.Nres`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_basisData_of_chartData_of_cocycle_of_comp_eq.GlueY3Sol.Nres_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_basisData_of_chartData_of_cocycle_of_comp_eq.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library).
Other imports: `Mathlib`.
