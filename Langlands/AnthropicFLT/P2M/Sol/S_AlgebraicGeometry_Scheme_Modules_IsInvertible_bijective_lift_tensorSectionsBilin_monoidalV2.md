# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_bijective_lift_tensorSectionsBilin_monoidalV2`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_bijective_lift_tensorSectionsBilin_monoidalV2.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 2 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- 1 `p2m_open "…"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions, `N~a~b` opening `N` with `a`, `b` hidden; it does not check that a namespace exists) are replaced by standard `open` commands with the same namespaces: `open _root_.N₁ _root_.N₂ …` for the namespaces without hidden names and one `open _root_.N hiding a b` per namespace with hidden names; a trailing ` in` is kept.
- 3 `p2m_open_scoped "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that activates the scoped extensions of the named namespaces without opening them) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces; a trailing ` in` is kept.
- 13 `p2m_export "N" "a b …"` command(s) (an FLT command from `P2M.Util` that adds aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) are replaced by `export _root_.N (a b …)` with the same names.
- Port edit (FLT line 18): the command `p2m_export "" "AlgebraicGeometry.Scheme.Modules.IsFrameOn.tensorSections"` is removed. Port edit: FLT `p2m_export "" "AlgebraicGeometry.Scheme.Modules.IsFrameOn.tensorSections"` (with the empty namespace) re-exports, at the root namespace, the private alias declared just above. Standard `export` needs a namespace, and within this file the private alias is already accessible by its full name, so the command is removed.
- Port edit (FLT line 28): the command `p2m_export "" "AlgebraicGeometry.Scheme.Modules.IsInvertible.tensor"` is removed. Port edit: FLT `p2m_export "" "AlgebraicGeometry.Scheme.Modules.IsInvertible.tensor"` (with the empty namespace) re-exports, at the root namespace, the private alias declared just above. Standard `export` needs a namespace, and within this file the private alias is already accessible by its full name, so the command is removed.
- Manual edit for Mathlib drift (FLT line 73, line 82 here): the FLT text
  `convert this using 1     funext a     rw [Module.algebraMap_end_apply, algebraMap_smul]   · intro y`
  is replaced by
  `convert this using 1   · intro y`.
  With the project's Mathlib, `convert this using 1` already closes the goal, so the following `funext a` and `rw` fail with `No goals to be solved` and are removed.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_bijective_lift_tensorSectionsBilin_monoidalV2.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_bijective_lift_tensorSectionsBilin_monoidalV2`. Statement. `AlgebraicGeometry.Scheme.Modules.IsInvertible.bijective_lift_tensorSectionsBilin_monoidalV2`: for invertible
modules `L`, `M` and an affine open `U`, the map `Γ(L, U) ⊗_{Γ(X,U)} Γ(M, U) → Γ(L ⊗ M, U)` is bijective.

Proof. Section `BasicOpen`: restriction of sections of a quasi-coherent module to a basic open is a
localization (`isLocalizedModule_resBO`, quasi-coherence from the ported
`OModulePresheaf.isQuasicoherent_ofModules_of_locallyTrivial`). Section `Theta`: the comparison map
`theta` and its localizations `thetaBO` are compatible. Section `Frames`: on basic opens where both `L`
and `M` have frames (ported `Scheme.Modules.exists_isFrameOn_of_pullback_iso_unit_monoidalV2`), the
comparison is bijective (`theta_bijective_of_isFrameOn`, with `IsFrameOn.tensorSections_monoidalV2`).
Section `Global`: such basic opens cover `U`, and a map of modules that becomes bijective after localizing
at the members of a finite cover by basic opens is bijective (`main`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_bijective_lift_tensorSectionsBilin_monoidalV2.AlgebraicGeometry.AlgebraicGeometry.AlgebraicGeometry.P2mPicCompareSol.modBO`
- scoped instance `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_bijective_lift_tensorSectionsBilin_monoidalV2.AlgebraicGeometry.AlgebraicGeometry.AlgebraicGeometry.P2mPicCompareSol.isScalarTower_modBO`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_bijective_lift_tensorSectionsBilin_monoidalV2.AlgebraicGeometry.AlgebraicGeometry.AlgebraicGeometry.P2mPicCompareSol.resBO`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_bijective_lift_tensorSectionsBilin_monoidalV2.AlgebraicGeometry.AlgebraicGeometry.AlgebraicGeometry.P2mPicCompareSol.resBO_apply`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_bijective_lift_tensorSectionsBilin_monoidalV2.AlgebraicGeometry.AlgebraicGeometry.AlgebraicGeometry.P2mPicCompareSol.toSpecTop`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_bijective_lift_tensorSectionsBilin_monoidalV2.AlgebraicGeometry.AlgebraicGeometry.AlgebraicGeometry.P2mPicCompareSol.isLocalizedModule_resBO`
- abbrev `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_bijective_lift_tensorSectionsBilin_monoidalV2.AlgebraicGeometry.AlgebraicGeometry.AlgebraicGeometry.P2mPicCompareSol.theta`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_bijective_lift_tensorSectionsBilin_monoidalV2.AlgebraicGeometry.AlgebraicGeometry.AlgebraicGeometry.P2mPicCompareSol.theta_tmul`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_bijective_lift_tensorSectionsBilin_monoidalV2.AlgebraicGeometry.AlgebraicGeometry.AlgebraicGeometry.P2mPicCompareSol.thetaBO`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_bijective_lift_tensorSectionsBilin_monoidalV2.AlgebraicGeometry.AlgebraicGeometry.AlgebraicGeometry.P2mPicCompareSol.thetaBO_tmul`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_bijective_lift_tensorSectionsBilin_monoidalV2.AlgebraicGeometry.AlgebraicGeometry.AlgebraicGeometry.P2mPicCompareSol.thetaBO_comp_map`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_bijective_lift_tensorSectionsBilin_monoidalV2.AlgebraicGeometry.AlgebraicGeometry.AlgebraicGeometry.P2mPicCompareSol.thetaBO_bijective_of`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_bijective_lift_tensorSectionsBilin_monoidalV2.AlgebraicGeometry.AlgebraicGeometry.AlgebraicGeometry.P2mPicCompareSol.res_self`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_bijective_lift_tensorSectionsBilin_monoidalV2.AlgebraicGeometry.AlgebraicGeometry.AlgebraicGeometry.P2mPicCompareSol.bijective_smul_of_isFrameOn`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_bijective_lift_tensorSectionsBilin_monoidalV2.AlgebraicGeometry.AlgebraicGeometry.AlgebraicGeometry.P2mPicCompareSol.theta_bijective_of_isFrameOn`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_bijective_lift_tensorSectionsBilin_monoidalV2.AlgebraicGeometry.AlgebraicGeometry.AlgebraicGeometry.P2mPicCompareSol.exists_basicOpen_isFrameOn`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_bijective_lift_tensorSectionsBilin_monoidalV2.AlgebraicGeometry.AlgebraicGeometry.AlgebraicGeometry.P2mPicCompareSol.main`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_bijective_lift_tensorSectionsBilin_monoidalV2.AlgebraicGeometry.AlgebraicGeometry.AlgebraicGeometry.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit_monoidalV2` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ofModules_of_locallyTrivial` (Library).
Other imports: `Mathlib`.
