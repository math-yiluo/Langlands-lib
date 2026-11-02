# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit`. Statement. `AlgebraicGeometry.OModulePresheaf.nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit`: let
`π : V ⟶ Spec R` be separated, `γ : W ⟶ V` affine, `K` an ordered affine cover of `V` and `N` a locally
trivial module on `V`. Then the Čech cohomology of `γ^* N` (over `γ ≫ π`) for the pulled-back cover
`K.comap γ` is isomorphic, in every degree, to the Čech cohomology for `K` of the twist
`(γ_* 𝒪_W) ⊗ N` of the pushforward of the structure sheaf (projection formula on Čech complexes).

Proof (namespace `P2mAffCech`). Section `Eta`: the unit `eta : Γ(N, U) → Γ(γ^* N, γ⁻¹ U)` of the
pullback–pushforward adjunction, additive and semilinear, natural in `U`. Section `Chart`: over an
affine open `U`, the map `theta : Γ(W, γ⁻¹ U) ⊗_{Γ(V, U)} Γ(N, U) → Γ(γ^* N, γ⁻¹ U)`, `b ⊗ s ↦ b · eta s`, is
bijective (`theta_bijective`, from the local triviality of `N` and the ported base-change of sections
`β` for invertible modules) and compatible with scalars and restriction. Section `Complex`: on the
intersections of the cover (affine, since `π` is separated and `γ` affine) these maps give a bijective
map of Čech complexes `phi` commuting with the differentials (`phi_bijective`, `d_phi`), hence the
isomorphisms of cohomology (`main_of_beta`, `main`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit.P2mAffCech.pb`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit.P2mAffCech.unitHom`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit.P2mAffCech.eta`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit.P2mAffCech.eta_add`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit.P2mAffCech.eta_smul`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit.P2mAffCech.app_map`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit.P2mAffCech.map_eta`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit.P2mAffCech.map_map`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit.P2mAffCech.map_self`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit.P2mAffCech.res_rfl`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit.P2mAffCech.appLE_rfl_apply`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit.P2mAffCech.algVW`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit.P2mAffCech.kappa`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit.P2mAffCech.kappa_apply`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit.P2mAffCech.Tobj`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit.P2mAffCech.theta`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit.P2mAffCech.theta_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit.P2mAffCech.theta_bijective`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit.P2mAffCech.theta_tmul`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit.P2mAffCech.theta_smulA`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit.P2mAffCech.theta_res`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit.P2mAffCech.res_app_algebraMap`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit.P2mAffCech.phiComp`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit.P2mAffCech.phiComp_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit.P2mAffCech.phiComp_bijective`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit.P2mAffCech.phi`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit.P2mAffCech.phi_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit.P2mAffCech.phi_bijective`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit.P2mAffCech.phiComp_res`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit.P2mAffCech.d_phi`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit.P2mAffCech.main_of_beta`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit.P2mAffCech.main`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafTensor` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_comp_d` (Library), `Langlands.AnthropicFLT.Theorems.Thm_LinearMap_exists_ker_linearEquiv_and_quotient_linearEquiv_of_surjective_of_forall_exact` (same contribution).
Other imports: `Mathlib`.
