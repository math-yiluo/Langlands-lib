# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

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

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom`.

Proof (namespace `P1Sol`): construction of the pullback `p^* G` along `p : V' ⟶ P` as compatible families of
local tensor products.

- Charts: a `Chart p` is a pair of affine opens `U ⊆ P`, `V ⊆ V'` with `V ⊆ p⁻¹ U`, ordered by inclusion of both
  (`le_def`, `le_rfl`, `le_trans'`), with ring map `φ : Γ(P, U) → Γ(V', V)` (`chartAlgebra`, `chart_algebraMap`,
  `rV_φ`; restriction maps `rV`, `rP`, `rV_refl`, `rV_rV`, `rP_rP`). `T c = Γ(V', V) ⊗_{Γ(P, U)} G(U)` with
  transition maps `tmap` for `c₁ ≤ c₂` (`tmap_tmul`, `tmap_refl`, `tmap_tmap`, `tmap_smul`, `tmapₗ`).
- Sections: over an open `W ⊆ V'`, `Fam` is the module of families indexed by charts with `V ⊆ W`
  (`ChartIn`; `Fam.*_apply`, `Fam.instModule`), and `Sec p G W` the submodule of `tmap`-compatible families
  (`Sec.compat`, `Sec.ext'`, `Sec.smul_apply`, `Sec.smulA_apply`, `Sec.moduleA` via `sc`, `rV_sc`,
  `algebraMap_eq_sc`), with restriction `resSec` (`resSec_apply`). `pullbackDatum p G` is the resulting FLT presheaf
  over `p ≫ q` (`pullbackDatum_obj`, `pullbackDatum_res_apply`), and `evₗ c` evaluates a section at the chart `c`
  (`evₗ_apply`, `evₗ_res`).
- Local structure, using quasi-coherence of `G`: shrinking `U` does not change `T` (`shrink`, `shrink_le`,
  `tmap_shrink_bijective`, from the ported theorem
  `IsQuasicoherent.exists_linearEquiv_tensorProduct_apply_one_tmul_eq_res`); passing to a basic open of `V` is a
  localization (`tmapₗ_isLocalizedModule'`, `rP_refl`, with the algebra lemmas `eq_of_forall_apply_eq`,
  `isLocalizedModule_of_smul_eq`). Charts can be refined to finite basic-open covers (`sub`, `sub_le`, `sub_le'`,
  `sub_V`, `exists_refinement`, `exists_chart_le_le`), so `T` and `Sec` satisfy the sheaf conditions for chart covers
  (`T_ext_of_cover'`, `Sec.ext_of_cover'`, `Sec.exists_of_cover'`, the gluing step using the ported theorem
  `IsLocalizedModule.exists_forall_apply_eq_of_span_range_eq_top`), and evaluation at a chart is bijective
  (`evₗ_bijective'`, `evₗ_bijective`, `evEquiv`, `evEquiv_apply`; non-primed versions re-exported).
- `eta U V h x = evEquiv⁻¹ (1 ⊗ x)` (`φ_algebraMap_eq_sc`, `eta`, `evEquiv_eta`); `Big`: finite chart covers of
  affines (`exists_finite_chartBasic_cover_le`, `exists_finite_chartBasic_cover`,
  `le_iSup_basicOpen_of_span_eq_top`, `exists_forall_ge_of_finite`); if `p` restricts to an isomorphism over `W`
  then `eta` is bijective there (`bijective_one_tmul_of_bijective_algebraMap`,
  `bijective_appLE_of_isIso_morphismRestrict`, `eta_bijective_of_isIso`, `eta_bijective`); coherence passes to the
  pullback (`finite_T`, `isCoherent`); `eta` is semilinear and compatible with both restrictions (`eta_smul`,
  `eta_res`, `eta_resU`), and `exists_beta` gives the base-change isomorphism
  `Γ(V', V) ⊗ G(U) ≅ p^*G(V)`.
- Quasi-coherence of the pullback: with charts `bchart`, `cut` over basic opens (`bchart_V`, `cut_le`, `cut_V`,
  `cut_V_le`, `cut_isLocalizedModule`, `cut_mono`), sections killed on `D(f)` are killed by a power of `f`
  (`exists_pow_smul_eq_zero_of_tmap_cut_eq_zero`, `pow_smul_eq_zero_of_le`, `exists_pow_smul_eq_zero`) and
  `f^n`-multiples of sections over `D(f)` extend (`exists_tmap_cut_eq_pow_smul`, `tmap_congr`, `tmap_comp`,
  `tmap_cut_sub_eq_zero`, `lift_mono`, `exists_res_eq_pow_smul`), giving `isQuasicoherent`.

`solution` returns `pullbackDatum p G` with `eta` and the listed properties.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.rV`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.rP`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.rV_refl`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.rV_rV`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.rP_rP`
- structure `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Chart`
- instance (anonymous, in namespace `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Chart`)
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Chart.le_def`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Chart.le_rfl`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Chart.le_trans'`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Chart.φ`
- instance `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.chartAlgebra`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.chart_algebraMap`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.rV_φ`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Chart.RU`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.T`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.tmap`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.tmap_tmul`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.tmap_refl`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.tmap_tmap`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.tmap_smul`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.ChartIn`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Fam`
- instance (anonymous, in namespace `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol`)
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Fam.add_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Fam.zero_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Fam.neg_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Fam.sub_apply`
- instance `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Fam.instSMul`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Fam.smul_apply`
- instance `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Fam.instModule`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Sec`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Sec.compat`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.sc`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.rV_sc`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.algebraMap_eq_sc`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Sec.moduleA`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.resSec`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.resSec_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Sec.ext'`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Sec.smul_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Sec.smulA_apply`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.pullbackDatum`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.pullbackDatum_obj`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.pullbackDatum_res_apply`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.evₗ`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.evₗ_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.evₗ_res`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.tmapₗ`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.shrink`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.shrink_le`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.tmap_shrink_bijective`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.rP_refl`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.tmapₗ_isLocalizedModule'`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.eq_of_forall_apply_eq`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.isLocalizedModule_of_smul_eq`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.sub`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.sub_le`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.sub_le'`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.sub_V`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.exists_refinement`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.exists_chart_le_le`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.T_ext_of_cover'`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Sec.ext_of_cover'`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Sec.exists_of_cover'`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.evₗ_bijective'`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.evₗ_bijective`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.evEquiv`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.evEquiv_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.φ_algebraMap_eq_sc`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.eta`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.evEquiv_eta`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.tmapₗ_isLocalizedModule`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.T_ext_of_cover`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Sec.ext_of_cover`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Sec.exists_of_cover`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Big.exists_finite_chartBasic_cover_le`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Big.exists_finite_chartBasic_cover`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Big.le_iSup_basicOpen_of_span_eq_top`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Big.exists_forall_ge_of_finite`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.P1Sol.Big.bijective_one_tmul_of_bijective_algebraMap`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.P1Sol.Big.bijective_appLE_of_isIso_morphismRestrict`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.P1Sol.P1Sol.Big.eta_bijective_of_isIso`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.P1Sol.P1Sol.Big.eta_bijective`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.P1Sol.P1Sol.Big.finite_T`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.P1Sol.P1Sol.Big.isCoherent`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.P1Sol.P1Sol.Big.eta_smul`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.P1Sol.P1Sol.Big.eta_res`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.P1Sol.P1Sol.Big.eta_resU`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.P1Sol.P1Sol.Big.exists_beta`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.P1Sol.P1Sol.Big.bchart`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.P1Sol.P1Sol.Big.bchart_V`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.P1Sol.P1Sol.Big.cut`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.P1Sol.P1Sol.Big.cut_le`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.P1Sol.P1Sol.Big.cut_V`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.P1Sol.P1Sol.Big.cut_V_le`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.P1Sol.P1Sol.Big.cut_isLocalizedModule`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.P1Sol.P1Sol.Big.exists_pow_smul_eq_zero_of_tmap_cut_eq_zero`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.P1Sol.P1Sol.Big.exists_tmap_cut_eq_pow_smul`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.P1Sol.P1Sol.Big.pow_smul_eq_zero_of_le`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.P1Sol.P1Sol.Big.exists_pow_smul_eq_zero`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.P1Sol.P1Sol.Big.tmap_congr`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.P1Sol.P1Sol.Big.tmap_comp`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.P1Sol.P1Sol.Big.cut_mono`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.P1Sol.P1Sol.Big.tmap_cut_sub_eq_zero`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.P1Sol.P1Sol.Big.lift_mono`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.P1Sol.P1Sol.Big.exists_res_eq_pow_smul`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.P1Sol.P1Sol.Big.isQuasicoherent`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.P1Sol.P1Sol.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafSectionsLinearRes` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_linearEquiv_tensorProduct_apply_one_tmul_eq_res` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isLocalizedModule_res_of_isQuasicoherent` (Library), `Langlands.AnthropicFLT.Theorems.Thm_IsLocalizedModule_exists_forall_apply_eq_of_span_range_eq_top` (same contribution).
Other imports: `Mathlib`.
