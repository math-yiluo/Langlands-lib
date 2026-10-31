# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_nonempty_iso_pullback_of_nonempty_iso_pullback_of_isDirectLimit`

## Source

Port of `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_nonempty_iso_pullback_of_nonempty_iso_pullback_of_isDirectLimit.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem
(commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2"). The text is the FLT text except for the changes listed below.
Licence: Apache License 2.0, Copyright 2026 Anthropic, PBC; unmodified copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice is recorded for it.
The Lean file starts with a notice recording the modification.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`,
  `backward.isDefEq.respectTransparency.types false`.
- `import P2M.Util` (the command library of FLT's build tooling) is dropped, and its commands are replaced by standard Lean commands. Write `N` for this file's namespace `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_nonempty_iso_pullback_of_nonempty_iso_pullback_of_isDirectLimit`. The `_root_.` prefix makes a name refer to the global namespace; inside `N` and its subnamespaces the plain name could resolve to a namespace of this file.
  - FLT line 19: `p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry N.AlgebraicGeometry TopologicalSpace Opposite TensorProduct"` becomes `open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct`. The namespace `N.AlgebraicGeometry` is omitted: at that point of the file it does not exist yet, and standard `open` rejects an unknown namespace, whereas `p2m_open` records the open declaration without checking. The file compiles without it.
  - FLT line 26: `p2m_export "AlgebraicGeometry" "…"` with 25 names becomes `export _root_.AlgebraicGeometry (…)` with the same names except: `Scheme.Hom.appInf`, `Scheme.Hom.appInf_apply`, `Scheme.Hom.appInf_map_left`, `Scheme.Hom.appInf_map_right`, `Scheme.Hom.preimage_mono_inf` are omitted: they are declared only later in this file, `p2m_export` skips names that do not exist yet, and standard `export` rejects them.
  - FLT line 28: `p2m_export "AlgebraicGeometry.Scheme" "…"` with 23 names becomes `export _root_.AlgebraicGeometry.Scheme (…)` with the same names except: `Hom.appInf`, `Hom.appInf_apply`, `Hom.appInf_map_left`, `Hom.appInf_map_right`, `Hom.preimage_mono_inf` are omitted: they are declared only later in this file, `p2m_export` skips names that do not exist yet, and standard `export` rejects them.
  - FLT line 30: `p2m_export "AlgebraicGeometry.Scheme.Modules" "…"` with 19 names becomes `export _root_.AlgebraicGeometry.Scheme.Modules (…)` with the same names.
  - FLT line 31: `p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"` becomes `open _root_.AlgebraicGeometry.Scheme.Modules _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry`.
  - FLT line 40: `p2m_export "AlgebraicGeometry.Scheme.Modules.Hom" "app_smul mapPresheaf comp_app id_app app"` becomes `export _root_.AlgebraicGeometry.Scheme.Modules.Hom (app_smul mapPresheaf comp_app id_app app)`.
  - FLT line 41: `p2m_open_scoped "AlgebraicGeometry.Scheme.Modules.Hom" in` becomes `open scoped _root_.AlgebraicGeometry.Scheme.Modules.Hom in`; both only activate the scoped declarations of the namespace for the next command.
  - FLT line 52: `p2m_alias "N.AlgebraicGeometry.Scheme.Hom.appInf" "AlgebraicGeometry.Scheme.Hom.appInf"` is deleted. It made `N.…` an alias of the private declaration declared just above. Nothing in the file refers to the alias name, and the file compiles without it.
  - FLT line 56: `p2m_alias "N.AlgebraicGeometry.Scheme.Hom.appInf_apply" "AlgebraicGeometry.Scheme.Hom.appInf_apply"` is deleted. It made `N.…` an alias of the private declaration declared just above. Nothing in the file refers to the alias name, and the file compiles without it.
  - FLT line 65: `p2m_alias "N.AlgebraicGeometry.Scheme.Hom.appInf_map_left" "AlgebraicGeometry.Scheme.Hom.appInf_map_left"` is deleted. It made `N.…` an alias of the private declaration declared just above. Nothing in the file refers to the alias name, and the file compiles without it.
  - FLT line 74: `p2m_alias "N.AlgebraicGeometry.Scheme.Hom.appInf_map_right" "AlgebraicGeometry.Scheme.Hom.appInf_map_right"` is deleted. It made `N.…` an alias of the private declaration declared just above. Nothing in the file refers to the alias name, and the file compiles without it.
  - FLT line 75: `p2m_export "AlgebraicGeometry.Scheme.Modules.IsFrameOn" "mono map existsUnique pullbackLocalSection"` becomes `export _root_.AlgebraicGeometry.Scheme.Modules.IsFrameOn (mono map existsUnique pullbackLocalSection)`.
  - FLT lines 77, 98, 108, 116, 130, 138, 145: `p2m_open_scoped "AlgebraicGeometry.Scheme.Modules.IsFrameOn" in` becomes `open scoped _root_.AlgebraicGeometry.Scheme.Modules.IsFrameOn in`; both only activate the scoped declarations of the namespace for the next command.
  - FLT line 91: `p2m_export "AlgebraicGeometry.Scheme.Modules" "IsFrameOn.unit_smul"` becomes `export _root_.AlgebraicGeometry.Scheme.Modules (IsFrameOn.unit_smul)`.
  - FLT line 106: `p2m_export "AlgebraicGeometry.Scheme.Modules" "IsFrameOn.existsUnique_self"` becomes `export _root_.AlgebraicGeometry.Scheme.Modules (IsFrameOn.existsUnique_self)`.
  - FLT line 114: `p2m_export "AlgebraicGeometry.Scheme.Modules" "IsFrameOn.smul_left_cancel"` becomes `export _root_.AlgebraicGeometry.Scheme.Modules (IsFrameOn.smul_left_cancel)`.
  - FLT line 124: `p2m_export "AlgebraicGeometry.Scheme.Modules" "IsFrameOn.smul_left_cancel'"` becomes `export _root_.AlgebraicGeometry.Scheme.Modules (IsFrameOn.smul_left_cancel')`.
  - FLT line 137: `p2m_export "AlgebraicGeometry.Scheme.Modules" "IsFrameOn.trans"` becomes `export _root_.AlgebraicGeometry.Scheme.Modules (IsFrameOn.trans)`.
  - FLT line 218: `p2m_export "AlgebraicGeometry.Scheme.Modules.IsInvertible" "pullback exists_trivialization"` becomes `export _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible (pullback exists_trivialization)`.
  - FLT line 220: `p2m_open_scoped "AlgebraicGeometry.Scheme.Modules.IsInvertible" in` becomes `open scoped _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible in`; both only activate the scoped declarations of the namespace for the next command.
  - FLT line 251: `p2m_export "AlgebraicGeometry.Scheme.Modules" "IsInvertible.exists_fin_affine_cover_isFrameOn₂"` becomes `export _root_.AlgebraicGeometry.Scheme.Modules (IsInvertible.exists_fin_affine_cover_isFrameOn₂)`.
  - FLT line 256: `p2m_open "AlgebraicGeometry.Scheme.Modules N.AlgebraicGeometry.Scheme.Modules"` becomes `open _root_.AlgebraicGeometry.Scheme.Modules N.AlgebraicGeometry.Scheme.Modules`.
  - FLT line 261: `p2m_alias "N.AlgebraicGeometry.Scheme.Hom.preimage_mono_inf" "AlgebraicGeometry.Scheme.Hom.preimage_mono_inf"` is deleted. It made `N.…` an alias of the private declaration declared just above. Nothing in the file refers to the alias name, and the file compiles without it.
- No other change: the declarations, statements and proofs are the FLT text.

## Contents

Declarations, with their original FLT names and namespaces (no new definitions or statements are introduced):

- lemma `presheaf_map_homOfLE_refl'`
- lemma `Hom.app_map_homOfLE`
- def `_root_.AlgebraicGeometry.Scheme.Hom.appInf`
- lemma `_root_.AlgebraicGeometry.Scheme.Hom.appInf_apply`
- lemma `_root_.AlgebraicGeometry.Scheme.Hom.appInf_map_left`
- lemma `_root_.AlgebraicGeometry.Scheme.Hom.appInf_map_right`
- lemma `_root_.AlgebraicGeometry.Scheme.Modules.IsFrameOn.unit_smul`
- lemma `presheaf_map_homOfLE_refl`
- lemma `_root_.AlgebraicGeometry.Scheme.Modules.IsFrameOn.existsUnique_self`
- lemma `_root_.AlgebraicGeometry.Scheme.Modules.IsFrameOn.smul_left_cancel`
- lemma `_root_.AlgebraicGeometry.Scheme.Modules.IsFrameOn.smul_left_cancel'`
- def `_root_.AlgebraicGeometry.Scheme.Modules.IsFrameOn.trans`
- lemma `IsFrameOn.trans_spec`
- lemma `IsFrameOn.app_trans_smul_pullbackLocalSection`
- lemma `exists_units_of_iso`
- lemma `nonempty_iso_of_units`
- lemma `_root_.AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_fin_affine_cover_isFrameOn₂`
- theorem `_root_.AlgebraicGeometry.Scheme.Hom.preimage_mono_inf`
- lemma `appInf_res`
- lemma `res_res`
- lemma `cocycle_res`
- lemma `map_swap`
- lemma `map_one_tmul`
- lemma `exists_ge₂`
- lemma `nonempty_iso_pullback_of_fac`
- theorem `solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_Mathlib_Algebra_IsDirectLimit`, `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor`, `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor`, `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection`, `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover`, `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_iso_app_eq_of_iSup_eq_top_of_forall_smul_eq`, `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_pullbackLocalSection`, `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit`, `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_algEquiv_sections_pullback_fst_preimage_tensor_of_isAffineOpen`, `Langlands.AnthropicFLT.Theorems.Thm_Algebra_TensorProduct_isDirectLimit_map_of_isDirectLimit`.
