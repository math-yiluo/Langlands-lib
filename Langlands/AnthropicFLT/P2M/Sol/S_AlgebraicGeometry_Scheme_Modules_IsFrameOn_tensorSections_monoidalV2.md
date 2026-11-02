# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 5 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- 2 `p2m_open "…"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions, `N~a~b` opening `N` with `a`, `b` hidden; it does not check that a namespace exists) are replaced by standard `open` commands with the same namespaces: `open _root_.N₁ _root_.N₂ …` for the namespaces without hidden names and one `open _root_.N hiding a b` per namespace with hidden names; a trailing ` in` is kept.
- 3 `p2m_export "N" "a b …"` command(s) (an FLT command from `P2M.Util` that adds aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) are replaced by `export _root_.N (a b …)` with the same names.
- Manual edit for Mathlib drift (FLT line 76, line 87 here): `erw [PresheafOfModules.map_smul, PresheafOfModules.Monoidal.tensorObj_map_tmul]` is replaced by `erw [PresheafOfModules.map_smul, PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul]`. In the project's Mathlib the lemma `tensorObj_map_tmul` (Mathlib `Algebra/Category/ModuleCat/Presheaf/Monoidal.lean`) is in namespace `PresheafOfModulesOfCommRing.Monoidal` instead of `PresheafOfModules.Monoidal`; the statement is the same.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2`. Statement. `AlgebraicGeometry.Scheme.Modules.IsFrameOn.tensorSections_monoidalV2`: if `s` is a frame of `L` and `t` a frame
of `M` on `V`, then `s ⊗ t` is a frame of `L ⊗ M` on `V`.

Proof. A frame on `V` is an isomorphism of the restriction to `V` with the structure sheaf given by the
section (`smulSectionHom`, `isIso_smulSectionHom`). Restricting to `V` (`restrictRingCatSheafHom`,
`restrictFunctor'`) and tensoring the two isomorphisms gives an isomorphism of `(L ⊗ M)|_V` with the
structure sheaf sending `1` to `s ⊗ t` (`τW`, local bijectivity `tsApp`), hence `s ⊗ t` is a frame
(`isFrameOn_tensorSections`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- lemma `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2.AlgebraicGeometry.Scheme.Modules.FrameTensor.bijective_smul_tmul`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2.AlgebraicGeometry.Scheme.Modules.FrameTensor.tsApp`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2.AlgebraicGeometry.Scheme.Modules.FrameTensor.tensorSections_eq_tsApp`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2.AlgebraicGeometry.Scheme.Modules.FrameTensor.tsApp_smul`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2.AlgebraicGeometry.Scheme.Modules.FrameTensor.tsApp_add`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2.AlgebraicGeometry.Scheme.Modules.FrameTensor.map_tsApp`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2.AlgebraicGeometry.Scheme.Modules.FrameTensor.map_smul_tmul`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2.AlgebraicGeometry.Scheme.Modules.FrameTensor.W_tensorSectionsHom`
- scoped instance `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2.AlgebraicGeometry.Scheme.Modules.FrameTensor.isLocallySurjective_tensorSectionsHom`
- scoped instance `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2.AlgebraicGeometry.Scheme.Modules.FrameTensor.isLocallyInjective_tensorSectionsHom`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2.AlgebraicGeometry.Scheme.Modules.FrameTensor.exists_local_preimage`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2.AlgebraicGeometry.Scheme.Modules.FrameTensor.exists_local_eq`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2.AlgebraicGeometry.Scheme.Modules.FrameTensor.restrictRingCatSheafHom`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2.AlgebraicGeometry.Scheme.Modules.FrameTensor.restrictFunctor'`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2.AlgebraicGeometry.Scheme.Modules.FrameTensor.image_le`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2.AlgebraicGeometry.Scheme.Modules.FrameTensor.image_preimage_of_le`
- abbrev `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2.AlgebraicGeometry.Scheme.Modules.FrameTensor.secX`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2.AlgebraicGeometry.Scheme.Modules.FrameTensor.smulSectionHom`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2.AlgebraicGeometry.Scheme.Modules.FrameTensor.smulSectionHom_app_apply`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2.AlgebraicGeometry.Scheme.Modules.FrameTensor.bijective_smul_map_iff_of_eq`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2.AlgebraicGeometry.Scheme.Modules.FrameTensor.bijective_smul_of_isIso`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2.AlgebraicGeometry.Scheme.Modules.FrameTensor.bijective_smul_tmul_res`
- abbrev `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2.AlgebraicGeometry.Scheme.Modules.FrameTensor.resL`
- abbrev `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2.AlgebraicGeometry.Scheme.Modules.FrameTensor.resM`
- abbrev `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2.AlgebraicGeometry.Scheme.Modules.FrameTensor.τW`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2.AlgebraicGeometry.Scheme.Modules.FrameTensor.map_τW`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2.AlgebraicGeometry.Scheme.Modules.FrameTensor.isIso_smulSectionHom`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2.AlgebraicGeometry.Scheme.Modules.FrameTensor.isFrameOn_tensorSections`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_PresheafOfModules_InternalHom` (Library), `Langlands.AnthropicFLT.Definitions.Def_SheafOfModules_MonoidalV2` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2` (Library).
Other imports: `Mathlib`.
