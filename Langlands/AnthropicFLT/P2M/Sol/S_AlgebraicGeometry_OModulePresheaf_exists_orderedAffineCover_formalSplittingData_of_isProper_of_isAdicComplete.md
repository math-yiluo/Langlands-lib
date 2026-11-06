# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Compatibility edit for the project's Mathlib: in the proof of `mem_span_of_isBaseChange`, the case `| zero => exact Submodule.zero_mem _` of `induction y using hf.inductionOn` is deleted. In this Mathlib, `IsBaseChange.inductionOn` has only the cases `tmul`, `smul` and `add`, so Lean rejects the `zero` case. The other cases are unchanged.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete`.

Proof (namespace `X1aRed`): the obstruction classes of the extension, computed chart by chart, form an approximate
Čech `0`-cocycle of `X = Ext¹(GE, GK)` converging `I`-adically.

- Section-level translations: `RW W = Γ(P, W)` is noetherian (`noeth`), coherent sections have finite free
  presentations (`exists_pres`), `I`-adic conditions over `A` and over `Γ(P, U)` agree (`JU`, `mem_bridge`,
  `pi_mem_smul_top`), and kernel, image and composition conditions transfer to the `Γ(P, U)`-linear maps
  `appSections` (`ker_appSections_eq`, `ker_appSections_le`, `range_appSections_eq_ker`, `comp_appSections_eq`,
  `comp_appSections_comm`).
- Restriction as flat base change (`algOf`, `modOf`, `towOf`, `mu`, `mu_apply`, `flatOf`, `mu_isBaseChange`,
  `map_refl`): `bc` restricts a presentation `f : RW W^r → F(W)` to `W' ⊆ W` (`ee`, `bc_apply`, `bc_apply_res`,
  `appSections_comp_bc`), and stays surjective (`mem_span_of_isBaseChange`, `bc_surjective`); `transport` moves
  obstruction data `δ` along restriction using the ported theorem
  `LinearMap.exists_isBaseChange_ker_span_range_eq_top_of_flat`. Index bookkeeping: `gres`, `gres_apply`,
  `gres_smul`, `gleft`, `gright`, `gleft_smul`, `gright_smul`, `π₁`, `π₂`, `π₁_append`, `π₂_append`, and for an
  ordered affine cover `K` the two charts `idx K s j` of a `1`-simplex (`inter_le_idx`, `Uc`, `hleD`); `PsD` is the
  sum presentation on the overlap (`PsD_append`).
- `chart_local`: on each chart, the ported theorem
  `LinearMap.exists_lifts_comp_eq_forall_comp_eq_comp_subtype_sub_mem_pow_smul_top` gives compatible lifts `ℓ` and
  a convergent sequence `δs` of obstruction data.
- `overlap_aux`: on an overlap, the two restricted classes differ by an element of `I^(n+1) X` (from the ported
  theorem `LinearMap.exists_forall_exists_finAppend_mkQ_sub_mkQ_mem_pow_smul_top` and the compatibility
  hypothesis `hXf`, applied to `transport`ed data); `d_zero_apply` unfolds the Čech differential.

`solution`: `P` is locally noetherian and compact; take an ordered affine cover `K` (ported theorem
`Scheme.nonempty_orderedAffineCover_of_compactSpace_univ`), presentations `pr i` of `GE` on the charts, chart data
from `chart_local`, constants `cO s` from the overlap lemma and their maximum `C`. With `δs i n = δL i (n + C)` and
`t n s` the class of `δs` on the first chart of `s` restricted to `s`, the required identities hold; `d (t n)` lies
in `I^(n+1) X` by `overlap_aux`, and `t (n+1) − t n ∈ I^(n+1) X` by the convergence of `δs`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.X1aRed.RW`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.X1aRed.noeth`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.X1aRed.exists_pres`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.X1aRed.JU`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.X1aRed.mem_bridge`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.X1aRed.pi_mem_smul_top`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.X1aRed.ker_appSections_eq`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.X1aRed.ker_appSections_le`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.X1aRed.range_appSections_eq_ker`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.X1aRed.comp_appSections_eq`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.X1aRed.comp_appSections_comm`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.X1aRed.algOf`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.X1aRed.modOf`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.X1aRed.towOf`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.X1aRed.mu`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.X1aRed.mu_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.X1aRed.flatOf`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.X1aRed.mu_isBaseChange`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.X1aRed.map_refl`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.X1aRed.ee`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.X1aRed.bc`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.X1aRed.bc_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.X1aRed.bc_apply_res`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.X1aRed.appSections_comp_bc`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.X1aRed.mem_span_of_isBaseChange`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.X1aRed.bc_surjective`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.X1aRed.transport`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.X1aRed.gres`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.X1aRed.gres_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.X1aRed.gres_smul`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.X1aRed.gleft`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.X1aRed.gright`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.X1aRed.gleft_smul`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.X1aRed.gright_smul`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.X1aRed.π₁`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.X1aRed.π₂`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.X1aRed.π₁_append`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.X1aRed.π₂_append`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.X1aRed.idx`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.X1aRed.inter_le_idx`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.X1aRed.Uc`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.X1aRed.chart_local`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.X1aRed.hleD`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.X1aRed.PsD`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.X1aRed.PsD_append`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.X1aRed.overlap_aux`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.X1aRed.d_zero_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover` (Library), `Langlands.AnthropicFLT.Theorems.Thm_LinearMap_exists_lifts_comp_eq_forall_comp_eq_comp_subtype_sub_mem_pow_smul_top` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_LinearMap_exists_forall_exists_finAppend_mkQ_sub_mkQ_mem_pow_smul_top` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_LinearMap_exists_isBaseChange_ker_span_range_eq_top_of_flat` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_linearEquiv_tensorProduct_apply_one_tmul_eq_res` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_nonempty_orderedAffineCover_of_compactSpace_univ` (same contribution).
Other imports: `Mathlib`.
