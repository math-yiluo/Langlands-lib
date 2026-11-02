# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 2 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- 1 `p2m_export "N" "a b …"` command(s) (an FLT command from `P2M.Util` that adds aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) are replaced by `export _root_.N (a b …)` with the same names.
- Manual edit for Mathlib drift (FLT line 353, line 364 here): the FLT text
  `convert hu using 1     exact e   · intro y`
  is replaced by
  `convert hu using 1   · intro y`.
  With the project's Mathlib, `convert hu using 1` already closes the goal, so the following `exact e` fails with `No goals to be solved` and is removed.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback`. Statement. `AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_baseChange_sections_linearEquiv_pullback`: for an
invertible module `L` on `X`, `p : Z ⟶ X`, and an affine open `U` of `X` with affine preimage, the sections of
the pullback over `p⁻¹ U` are `Γ(Z, p⁻¹ U) ⊗_{Γ(X, U)} Γ(L, U)`, by an isomorphism `β` with
`β (1 ⊗ s) = (unit of the pullback–pushforward adjunction) s`.

Proof. Sections `Res`, `EvalFrame`: on an open where `L` has a frame (ported
`Scheme.Modules.exists_isFrameOn_of_pullback_iso_unit`), sections are coefficient multiples of the frame
(`coef`, `liftFun`, `eval_bijective`). Section `Pull`: the unit `eta : Γ(L, U) → Γ(p^* L, p⁻¹ U)` sends a
frame to a frame (`evalPull_bijective`, `bijective_smul_eta`). Section `Affine`: both sides are
quasi-coherent (ported `OModulePresheaf.isQuasicoherent_ofModules_of_locallyTrivial`), the comparison map
`b ⊗ s ↦ b · eta s` is compatible with localization at basic opens
(`isLocalizedModule_powers_of_comap`), and bijective on the basic opens where `L` is trivial, hence
bijective on `p⁻¹ U`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.map_map`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.map_self`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.fmap_map`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.fmap_self`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.bijective_map_of_eq`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.app_map`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.eval_injective`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.liftFun`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.coef`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.coef_spec`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.coef_unique`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.coef_add`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.coef_smul`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.map_coef`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.liftFun_spec`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.liftFun_add`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.liftFun_smul`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.liftFun_map`
- private def `P2mPullbackSectionsSol.lift`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.lift_app`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.lift_app_self`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.eval_bijective`
- abbrev `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.pb`
- abbrev `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.unitHom`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.eta`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.eta_add`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.eta_smul`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.map_eta`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.evalPull_eq`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.evalPull_bijective`
- abbrev `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.OO`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.toFun'`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.ofFun'`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.toFun'_ofFun'`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.toFun'_injective`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.toFun'_smul`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.toFun'_zero`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.toFun'_map`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.OO_map_bijective`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.ιapp_injective`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.ιapp_bijective`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.ιapp_map`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.preimage_inf_eq`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.bijective_smul_eta`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.isLocalizedModule_powers_of_comap`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.algAB`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.modAN`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.algebraMap_AB`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.smul_AN`
- scoped instance `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.isScalarTower_ABN`
- scoped instance `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.smulCommClass_ABN`
- scoped instance `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.smulCommClass_BAN`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.thetaFix`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.thetaBilin`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.theta`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.theta_tmul`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.modAZW`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.modANW`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.appLE_apply`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.resB`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.resN`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.isLocalizedModule_resB_of_eq`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.modBO`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.resBO`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.isLocalizedModule_resBO`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.isLocalizedModule_resN_of_eq`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.pre_le`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.modAZ`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.modANr`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.smul_AZ`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.smul_ANr`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.smul_BO`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.app_res`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.thetaLoc`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.thetaLoc_tmul`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.resT`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.thetaA`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.thetaA_apply`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.thetaLoc_comp_resT`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.thetaLoc_bijective_of_frame`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.exists_basicOpen_isFrameOn`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.theta_bijective`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.beta`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.beta_tmul`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.beta_one_tmul`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol.result`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ofModules_of_locallyTrivial` (Library).
Other imports: `Mathlib`.
