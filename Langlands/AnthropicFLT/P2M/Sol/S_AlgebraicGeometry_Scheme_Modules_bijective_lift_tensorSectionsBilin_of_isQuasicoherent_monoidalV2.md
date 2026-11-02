# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 2 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- 1 `p2m_open "…"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions, `N~a~b` opening `N` with `a`, `b` hidden; it does not check that a namespace exists) are replaced by standard `open` commands with the same namespaces: `open _root_.N₁ _root_.N₂ …` for the namespaces without hidden names and one `open _root_.N hiding a b` per namespace with hidden names; a trailing ` in` is kept.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2`. Statement. `AlgebraicGeometry.Scheme.Modules.bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2`: for modules
`L`, `M` with quasi-coherent FLT presheaves and an affine open `U`, the map
`Γ(L, U) ⊗_{Γ(X,U)} Γ(M, U) → Γ(L ⊗ M, U)` is bijective.

Proof. Section `BasicOpen`: restriction to basic opens is a localization for quasi-coherent modules.
Section `Theta`: the comparison `theta` and its localized versions `thetaBO` on basic opens, with
`tensorBOEquiv` identifying the localized tensor product. Section `Local`: the presheaf map `phi` from the
presheaf tensor product to the sheaf tensor product is locally injective and locally surjective (it is
the sheafification map), so for each section of `L ⊗ M` over `U` there is a cover by basic opens on which
it comes from `Γ(L) ⊗ Γ(M)` (sections `Extract`, `Surjective`), and injectivity is checked after localizing
(section `Injective`); glue with the localization property to get bijectivity over `U`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2.P2mQcTensorCompare.modBO`
- scoped instance `P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2.P2mQcTensorCompare.isScalarTower_modBO`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2.P2mQcTensorCompare.resBO`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2.P2mQcTensorCompare.resBO_apply`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2.P2mQcTensorCompare.isLocalizedModule_resBO`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2.P2mQcTensorCompare.res_resBO`
- abbrev `P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2.P2mQcTensorCompare.theta`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2.P2mQcTensorCompare.theta_tmul`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2.P2mQcTensorCompare.thetaBO`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2.P2mQcTensorCompare.thetaBO_tmul`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2.P2mQcTensorCompare.thetaBO_comp_map`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2.P2mQcTensorCompare.thetaBO_map`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2.P2mQcTensorCompare.tensorBOEquiv`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2.P2mQcTensorCompare.tensorBOEquiv_tmul`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2.P2mQcTensorCompare.thetaBO_tensorBOEquiv`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2.P2mQcTensorCompare.thetaBO_injective_of`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2.P2mQcTensorCompare.phi`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2.P2mQcTensorCompare.phi_isLocallyInjective`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2.P2mQcTensorCompare.phi_isLocallySurjective`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2.P2mQcTensorCompare.phiU`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2.P2mQcTensorCompare.phiU_eq_theta`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2.P2mQcTensorCompare.resT`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2.P2mQcTensorCompare.resT_tmul`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2.P2mQcTensorCompare.resT_comp`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2.P2mQcTensorCompare.exists_resT_eq_of_theta_eq`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2.P2mQcTensorCompare.exists_theta_eq_res`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2.P2mQcTensorCompare.theta_resT`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2.P2mQcTensorCompare.tensorBOEquiv_resT`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2.P2mQcTensorCompare.theta_injective`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2.P2mQcTensorCompare.exists_basicOpen_theta_res`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2.P2mQcTensorCompare.bump`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2.P2mQcTensorCompare.exists_pow_smul_sub_eq_zero`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2.P2mQcTensorCompare.theta_surjective`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2.P2mQcTensorCompare.theta_bijective`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules` (Library).
Other imports: `Mathlib`.
