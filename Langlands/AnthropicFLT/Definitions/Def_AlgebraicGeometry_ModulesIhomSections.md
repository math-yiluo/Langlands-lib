# `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesIhomSections`

## Source

Port of `Definitions/Def_AlgebraicGeometry_ModulesIhomSections.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem
(commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2"). The text is the FLT text except for the changes listed below.
Licence: Apache License 2.0, Copyright 2026 Anthropic, PBC; unmodified copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice is recorded for it.
The Lean file starts with a notice recording the modification.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`,
  `backward.isDefEq.respectTransparency.types false`.
- No other change: the declarations, statements and proofs are the FLT text.

## Contents

Declarations, with their original FLT names and namespaces (no new definitions or statements are introduced):

- def `toPresheafHom`
- abbrev `appAt`
- lemma `appAt_toPresheafHom`
- def `linearSub`
- def `ofPresheafHom`
- lemma `ofPresheafHom_app`
- def `equivLinearSub`
- def `isoLinearSub`
- lemma `linearSub_local`
- theorem `PresheafOfModules.ihomObj_isSheaf`
- lemma `ihom_obj_eq_ihomObj`
- lemma `ihom_map_app_val`
- lemma `ihom_adjunction_unit_app_val`
- lemma `ihom_adjunction_counit_app`
- theorem `unitIsoSelf_hom_eq`
- lemma `sheafify_map_val_app_unit`
- lemma `counit_val_app_unit`
- lemma `toPMod_obj_map_apply`
- abbrev `ihomModel`
- theorem `isSheaf_ihomModel`
- theorem `ihom_obj_eq`
- def `ihomModelToIhom`
- instance `isIso_ihomModelToIhom`
- def `ihomModelSectionsIso`
- def `ihomSectionsEquivFamily`
- lemma `ihomSectionsEquivFamily_symm_apply`
- lemma `ihomSectionsEquivFamily_apply`
- lemma `ihomSectionsEquivFamily_unit`
- lemma `unit_ihomSectionsEquivFamily`
- lemma `ihomSectionsEquivFamily_map`
- lemma `ihomSectionsEquivFamily_map_app`
- def `ihomEval`
- lemma `ihomEval_def`
- lemma `ihomSectionsEquivFamily_app_eq_ihomEval`
- lemma `ihomEval_unit_app`
- lemma `map_ihomEval`
- lemma `ihom_sections_ext`
- lemma `ihomEval_add_right`
- lemma `ihomEval_add_left`
- lemma `ihomEval_smul_left`
- lemma `ihomEval_smul_right`
- def `sheafifyTensorIso`
- lemma `sheafifyTensorIso_hom_naturality`
- def `sheafifyTensorNatIso`
- lemma `sheafifyTensorNatIso_hom_app`
- def `unitIhomNatIso`
- lemma `unitIhomNatIso_hom_app`
- theorem `ihom_adjunction_eq`
- def `tmulSection`
- lemma `tmulSection_def`
- lemma `tensorHom_val_app_tmulSection`
- lemma `whiskerLeft_val_app_tmulSection`
- lemma `whiskerRight_val_app_tmulSection`
- lemma `map_tmulSection`
- lemma `tmulSection_add_left`
- lemma `tmulSection_add_right`
- lemma `tmulSection_smul_left`
- lemma `tmulSection_smul_right`
- lemma `toPMod_map_curry`
- theorem `ihomSectionsEquivFamily_curry_app`
- theorem `ihomEval_curry`
- theorem `ihom_ev_val_app_tmulSection`
- theorem `uncurry_val_app_tmulSection`
- theorem `ihom_hom_ext`
- theorem `tensor_hom_ext`
- theorem `ihomEval_ihom_map_val_app`
- theorem `ihomEval_pre_val_app`
- lemma `ε_sheafifyFunctor`
- lemma `sheafifyUnitIso_hom_eq_counit`
- lemma `sheafifyTensorIso_hom_leftUnitor_hom`
- theorem `leftUnitor_hom_val_app_tmulSection`
- theorem `leftUnitor_inv_val_app`
- theorem `unitIsoSelf_hom_val_app`
- abbrev `toPMod`
- lemma `toPMod_obj_map_apply`
- lemma `image_preimage_eq_of_le`
- abbrev `opHomImage`
- lemma `restrict_ringHom_apply`
- lemma `restrict_smul_eq`
- def `restrictHomOfFamily`
- lemma `restrictHomOfFamily_app_apply`
- def `restrictHomAppLE`
- lemma `restrictHomAppLE_apply`
- lemma `map_restrictHomAppLE`
- lemma `restrictHomAppLE_image`
- def `familyOfRestrictHom`
- lemma `familyOfRestrictHom_app`
- def `restrictHomEquivFamily`
- lemma `restrictHomEquivFamily_apply`
- lemma `restrictHomEquivFamily_symm_apply`
- def `ihomEval`
- theorem `tmulSection_eq_tensorSections`
- lemma `map_ihomEval`
- lemma `ihom_sections_ext`
- lemma `ihomEval_add_left`
- lemma `ihomEval_add_right`
- lemma `ihomEval_smul_left`
- lemma `ihomEval_smul_right`
- lemma `ihomEval_zero_left`
- lemma `ihomEval_zero_right`
- theorem `ihomEval_curry_app`
- theorem `ihom_ev_app_tensorSections`
- theorem `uncurry_app_tensorSections`
- theorem `ihom_hom_ext`
- theorem `tensor_hom_ext`
- theorem `ihomEval_ihom_map_app`
- theorem `ihomEval_pre_app`
- theorem `unitIsoSelf_hom_app`
- def `ihomSectionsEquiv`
- lemma `ihomSectionsEquiv_apply`
- lemma `ihomSectionsEquiv_symm_apply`
- theorem `ihomSectionsEquiv_app_apply`
- theorem `ihomEval_map_ihomSectionsEquiv_symm`
- theorem `ihomEval_map_ihomSectionsEquiv_symm_image`
- lemma `ihomEval_eqToHom`
- theorem `ihomSectionsEquiv_map_app_apply`
- def `homOfFamily`
- lemma `homOfFamily_app_apply`
- def `familyOfHom`
- lemma `familyOfHom_app`
- def `homEquivFamily`
- def `ihomGlobalSectionsEquiv`
- theorem `ihomGlobalSectionsEquiv_app_apply`
- theorem `ihomEval_map_ihomGlobalSectionsEquiv_symm`
- theorem `ihomEval_ihomGlobalSectionsEquiv_symm`
- theorem `ihomSectionsEquiv_map_app_apply_of_top`
- def `restrictUnitIso'`
- lemma `restrictUnitIso_hom_app_apply`
- lemma `restrictUnitIso_inv_app_apply`
- lemma `restrictUnitIso_ι_hom_app_apply`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_PresheafOfModules_InternalHom`, `Langlands.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal`, `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor`.
