# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_chartData_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_chartData_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartData_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_chartData_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete`.

Proof (namespace `RedX1`).

- Helpers: `I`-adic membership is preserved by linear maps and agrees over `A` and over `Γ(P, U)`
  (`mem_smul_top_map`, `mem_map_pow_smul_top_iff`), lifts from quotients (`mem_smul_top_sup_of_mkQ`), standard
  basis vectors (`e`, `e_map`, `apply_eq_sum_e`); `thetaC`/`theta` is the map
  `ExtPushout pU dU → FU` given by `lamC` on `inl` and `v ↦ ∑ v_m w_m` on `inr` (`thetaC_inl`, `thetaC_inr`,
  `theta_apply`; `isScalarTower_compHom`); simplices of an ordered cover (`vtx`, `le_inter_vtx`, `strictMono_pair`,
  `edge`, `edge_val_zero`, `edge_val_one`, `face_edge_zero`, `face_edge_one`, `le_inter_edge`), and a Čech `0`-cocycle
  has equal restrictions from two charts (`res_vtx_eq_of_d_eq_zero`).
- `stageA`: the ported theorem `exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete` gives
  an ordered affine cover with chart presentations, lifts and approximate cocycles `t n` of `X = Ext¹(GE, GK)`;
  the ported theorem `existsUnique_d_eq_zero_forall_sub_mem_pow_smul_of_isAdicComplete_of_isProper` (`A` complete,
  `q` proper) gives a true cocycle `a` with `a − t n ∈ I^(n+1) X`. Representing `a` on each chart by some
  `δ i : ker (pr i) → GK`, the ported theorem
  `LinearMap.exists_forall_comp_eq_comp_subtype_eq_of_forall_sub_mem_pow_smul_sup_range` gives compatible lifts
  `ℓ'` restricting to `lam ∘ δ i`, and the classes of the `δ i` agree on overlaps (`res_vtx_eq_of_d_eq_zero`).

`solution`: build `X` with the ported theorem `exists_isCoherent_linearEquiv_extQuot_of_isCoherent`, apply `stageA`,
and take the chart models and overlap isomorphisms from the ported theorem
`exists_chartModels_extPushout_of_forall_res_symm_mk_eq`. The maps `θF i k U` are `theta` built from `lam k` and
the restricted lifts `ℓ'`; their compatibilities `hc1`–`hc3` and with restriction are checked on `inl` and `inr`
(every element of a pushout is `inl n + inr v`), using that the image of `gU` spans the kernel.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartData_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.RedX1.mem_smul_top_map`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartData_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.RedX1.mem_map_pow_smul_top_iff`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartData_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.RedX1.mem_smul_top_sup_of_mkQ`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartData_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.RedX1.e`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartData_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.RedX1.e_map`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartData_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.RedX1.apply_eq_sum_e`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartData_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.RedX1.thetaC`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartData_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.RedX1.thetaC_inl`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartData_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.RedX1.thetaC_inr`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartData_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.RedX1.theta`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartData_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.RedX1.theta_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartData_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.RedX1.isScalarTower_compHom`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartData_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.RedX1.vtx`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartData_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.RedX1.le_inter_vtx`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartData_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.RedX1.strictMono_pair`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartData_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.RedX1.edge`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartData_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.RedX1.edge_val_zero`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartData_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.RedX1.edge_val_one`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartData_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.RedX1.face_edge_zero`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartData_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.RedX1.face_edge_one`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartData_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.RedX1.le_inter_edge`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartData_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.RedX1.res_vtx_eq_of_d_eq_zero`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartData_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.RedX1.stageA`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartData_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.Definitions.Def_LinearMap_ExtPushout` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_existsUnique_d_eq_zero_forall_sub_mem_pow_smul_of_isAdicComplete_of_isProper` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_chartModels_extPushout_of_forall_res_symm_mk_eq` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_LinearMap_exists_forall_comp_eq_comp_subtype_eq_of_forall_sub_mem_pow_smul_sup_range` (same contribution).
Other imports: `Mathlib`.
