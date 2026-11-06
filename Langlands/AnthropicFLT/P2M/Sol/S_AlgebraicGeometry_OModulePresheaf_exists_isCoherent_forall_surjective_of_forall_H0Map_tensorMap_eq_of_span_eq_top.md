# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

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

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top`.

Proof (namespace `P2mUntwist`): `E = O(-d)^m` and the compatible sections `σ k l` of `F k ⊗ O(d)` give compatible
surjections `E → F k`.

- Generic: `restrictFun_injective_of_ge`, `res_res_eq_self`, quasi-coherence of the unit presheaf and of powers
  (`isQuasicoherent_unit`, `isQuasicoherent_pow'`), `twistObj_sub_val`.
- The presheaf `E`: `Xsec a` is the section "`X_a^d`" of the twist `O(d)` (components `u_{ka}^d`; `Xsec_val`,
  `res_Xsec`). `η : Src → Tgt` sends a family `f l i` of functions (`l < m`, `i ≤ r`) to
  `f l i · X_a^d − f l a · X_i^d` (`ηfun`, `ηfun_apply`, `ηfun_add`, `ηfun_smul`, `res_ηfun`, `η_app_apply`), and
  `E = ker η` (quasi-coherent: `isQuasicoherent_E`; coordinates `cf`). On an open `W` inside chart `j`, elements of `E`
  satisfy `cf e l i = u_{ji}^d · cf e l j` (`ker_comp`), so evaluation at the `j`-components is an isomorphism
  `chartE : E(W) ≅ Γ(W)^m` (`evE`, `liftE`, `ηfun_liftFun_eq_zero`, `evE_liftE`, `liftE_evE`, `evE_surjective`,
  `evE_res`; changing chart multiplies by `u_{jj'}^d`, `evE_change`).
- Coherence: on an affine `U`, functions `f` with `D(f)` inside some chart generate the unit ideal
  (`smallFuns`, `span_smallFuns`); on such `D(f)` the sections are the localization (`moduleU`, `isScalarTower_U`,
  `isLocalization_U`, `isLocalizedModule_res`) and finite free (`finite_local`), hence `E(U)` is finite (`finite`,
  `isCoherent_E`).
- Untwisting: `evT` trivializes `O(d)` on chart `j` (`restrictFun_evT`, `evT_res`, `evT_change`), giving
  `untw : G ⊗ O(d) → G` there (`untw_tmul`, `untw_surjective`, `res_untw`, `untw_change`, `app_untw`).
- `Θ`: for `0`-simplices `s` with chart `ch s` (`inter_le_ch`), `sk τ s` is the untwisted restriction of a cochain
  (`sk_def`, `res_sk`), and `θloc τ s e = ∑_l (evE e)_l · sk (τ l) s` is a local homomorphism `E → G`
  (`θloc_apply`, `res_θloc`), giving sections `homFam` of the ported internal Hom (`homFam_apply`). For cocycles
  `τ l ∈ H0` these agree on overlaps (`res_face_eq`, `d_homFam`), so by the gluing property of the internal Hom into a
  quasi-coherent presheaf (ported theorem `internalHom_d_zero_eq_zero_iff_existsUnique`) they glue uniquely (`existsUnique_hom`) to `Θ τ : AffHom E G` (`Θ_spec`, `Θ_app`,
  `Θ_unique`), natural in `G` (`app_sk`).
- Nakayama: `I^(k+1)` kills `F k` on affines (`pow_smul_top_eq_bot`), so lifts along the surjections `φ k` of
  generators generate (`span_eq_top_of_span_image_eq_top`).
- Local surjectivity: if the components `τ l s` generate over `W s`, then the `sk (τ l) s` generate over any affine
  basic open inside it (`span_sk_eq_top`); compatibility of the `σ k` (`σ_step`, `app_sk_succ`) and Nakayama
  propagate generation from level `0` to all `k` (`span_sk_eq_top_all`), so `Θ (σ k)` is surjective there
  (`surjective_local`). Surjectivity of a map of quasi-coherent presheaves on an affine follows from surjectivity
  on the members of a cover by basic opens (`surjective_of_forall_basicOpen`).
- `main`: the basic opens `D(f) = D(g)` for `g` a function on some `W s` (`biBasic`, `vtx`, `U_le_inter_vtx`)
  generate (`span_biBasic`), so `Θ (σ k)` is surjective on every affine (`surjective_Θ`); compatibility with the
  `φ k` holds by uniqueness of `Θ` (`comp_Θ`). Then `E` with the `Θ (σ k)` is the required presheaf.
  `solution` is `P2mUntwist.main`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.restrictFun_injective_of_ge`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.res_res_eq_self`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.isQuasicoherent_unit`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.isQuasicoherent_pow'`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.twistObj_sub_val`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.Xsec`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.Xsec_val`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.res_Xsec`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.Src`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.Tgt`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.ηfun`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.ηfun_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.ηfun_add`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.ηfun_smul`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.res_ηfun`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.η`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.η_app_apply`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.E`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.isQuasicoherent_E`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.cf`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.ker_comp`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.evE`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.evE_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.ηfun_liftFun_eq_zero`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.liftE`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.liftE_val`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.evE_liftE`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.liftE_evE`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.evE_surjective`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.chartE`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.evE_res`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.evE_change`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.smallFuns`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.span_smallFuns`
- instance `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.moduleU`
- instance `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.isScalarTower_U`
- instance `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.isLocalization_U`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.isLocalizedModule_res`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.finite_local`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.finite`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.isCoherent_E`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.evT`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.restrictFun_evT`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.evT_res`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.evT_change`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.untw`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.untw_tmul`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.untw_surjective`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.res_untw`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.untw_change`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.app_untw`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.ch`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.inter_le_ch`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.sk`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.sk_def`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.res_sk`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.θloc`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.θloc_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.res_θloc`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.homFam`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.homFam_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.res_face_eq`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.d_homFam`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.existsUnique_hom`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.Θ`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.Θ_spec`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.Θ_app`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.Θ_unique`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.app_sk`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.pow_smul_top_eq_bot`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.span_eq_top_of_span_image_eq_top`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.span_sk_eq_top`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.σ_step`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.app_sk_succ`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.span_sk_eq_top_all`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.surjective_local`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.surjective_of_forall_basicOpen`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.biBasic`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.vtx`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.U_le_inter_vtx`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.span_biBasic`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.surjective_Θ`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.comp_Θ`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist.main`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafTensorMap` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjTwistDatum` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafInternalHom` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafSectionsLinearRes` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_linearEquiv_twistObj_of_le_pullbackChart` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_isQuasicoherent_twist` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ker` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isLocalizedModule_res_of_isQuasicoherent` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique` (same contribution).
Other imports: `Mathlib`.
