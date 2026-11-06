# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Compatibility edit for the project's Mathlib: in the proof of `mem_span_of_isBaseChange`, the case `| zero => exact Submodule.zero_mem _` of `induction y using hf.inductionOn` is deleted. In this Mathlib, `IsBaseChange.inductionOn` has only the cases `tmul`, `smul` and `add`, so Lean rejects the `zero` case. The other cases are unchanged.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.solution` proves the
statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective`.

Proof (namespace `X1bSol`): the pushout extensions `ExtPushout (prU U) (δU U)` over the affine opens `U ⊆ U₀` form
basis data for a quasi-coherent sheaf.

- `EP` (pushout extensions, using the ported definitions in `Definitions.Def_LinearMap_ExtPushout`): semilinear
  universal property `slift` (`slift_mk`, `slift_inl`, `slift_inr`), induction and extensionality (`ind`,
  `fun_ext`); restriction maps `resMap` along a ring map `σ` induced by componentwise `σ` on `B^r` (`coordMap`,
  `coordMap_apply`, `coordMap_mem_ker`, `resMap_inl`, `resMap_inr`, `resMap_mk`); for a localization `σ` at `g₀`,
  `resMap` is surjective up to powers of `g₀` and its kernel is `g₀`-power torsion (`exists_vec_lift`,
  `resMap_surj_upto`, `resMap_ker_torsion`); compatibility with `proj`, identity and composition (`proj_resMap`,
  `resMap_self`, `resMap_trans`); restriction of scalars to `A` (`linA`, `inlA`, `projA`, `linA_apply`,
  `isScalarTower_compHom`, `range_inlA_eq_ker_projA`); finiteness (`finite_extPushout`).
- `BC` (base change of presentations along flat maps): `φ`, `φ_apply`, `isBaseChange_φ`,
  `mem_span_of_isBaseChange`; `bc` restricts the presentation (`bc_apply`, `bc_φ`, `bc_algebraMap`,
  `surjective_of_isBaseChange`); `g` maps kernels (`g_coe`, `g_coe_apply`) and is a base change whose image spans
  (`isBaseChange_g`, `span_range_g_eq_top`, `span_range_g`), so maps out of `ker p'` are determined on the image of
  `g` (`ext_on_g`, `ext_of_span_eq`); `δ'` is the base change of `δ` (`δ'_g`).
- `SG` (scheme geometry): restriction ring maps `ρ` (`ρ_refl_apply`, `ρ_ρ`, `ρ_algebraMap`), flat between affine
  opens (`flat_ρ`); semilinear restriction `resₛ` (`resₛ_apply`); quasi-coherence and localization on basic opens
  (`qc_of_eq`, `loc_of_eq`); restriction of a quasi-coherent presheaf is a base change (`isBaseChange_res`).
- Chart data: `chart_kit` restricts `pr` and `δ` to every affine `U ⊆ U₀` (presentation `prU U`, kernel map
  `gU U`, base-changed `δU U` with spanning image); these restrictions are compatible (`chart_prUn`, `chart_memn`,
  `chart_δUn`), and `Rmap` is the induced restriction between pushouts.

`solution` returns these data, with `res = linA Rmap`, `ϑ = inl` and `θE = proj` (restricted to `A`); exactness of
`0 → GK → ExtPushout → GE → 0`, finiteness, functoriality of `res` and the quasi-coherence conditions `hqc` (from
`resMap_surj_upto`, `resMap_ker_torsion`) follow from the lemmas above.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.EP.slift`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.EP.slift_mk`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.EP.slift_inl`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.EP.slift_inr`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.EP.ind`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.EP.fun_ext`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.BC.φ`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.BC.φ_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.BC.isBaseChange_φ`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.BC.mem_span_of_isBaseChange`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.BC.bc`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.BC.bc_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.BC.bc_φ`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.BC.bc_algebraMap`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.BC.surjective_of_isBaseChange`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.BC.g`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.BC.g_coe`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.BC.g_coe_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.BC.isBaseChange_g`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.BC.span_range_g_eq_top`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.BC.span_range_g`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.BC.ext_on_g`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.BC.ext_of_span_eq`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.BC.δ'`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.BC.δ'_g`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.EP.coordMap`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.EP.coordMap_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.EP.coordMap_mem_ker`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.EP.resMap`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.EP.resMap_inl`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.EP.resMap_inr`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.EP.resMap_mk`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.EP.exists_vec_lift`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.EP.resMap_surj_upto`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.EP.resMap_ker_torsion`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.SG.ρ`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.SG.ρ_refl_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.SG.ρ_ρ`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.SG.ρ_algebraMap`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.SG.flat_ρ`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.SG.resₛ`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.SG.resₛ_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.SG.qc_of_eq`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.SG.loc_of_eq`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.SG.isBaseChange_res`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.EP.linA`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.EP.inlA`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.EP.projA`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.EP.linA_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.EP.proj_resMap`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.EP.resMap_self`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.EP.resMap_trans`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.EP.isScalarTower_compHom`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.EP.range_inlA_eq_ker_projA`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.EP.finite_extPushout`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.chart_kit`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.chart_prUn`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.chart_memn`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.chart_δUn`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.X1bSol.Rmap`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.Definitions.Def_LinearMap_ExtPushout` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_linearEquiv_tensorProduct_apply_one_tmul_eq_res` (same contribution).
Other imports: `Mathlib`.
