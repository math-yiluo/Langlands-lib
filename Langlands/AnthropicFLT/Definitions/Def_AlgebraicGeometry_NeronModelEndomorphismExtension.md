# `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension`

## Source

Port of `Definitions/Def_AlgebraicGeometry_NeronModelEndomorphismExtension.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem
(commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2"). The text is the FLT text except for the changes listed below.
Licence: Apache License 2.0, Copyright 2026 Anthropic, PBC; unmodified copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice is recorded for it.
The Lean file starts with a notice recording the modification.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`,
  `backward.isDefEq.respectTransparency.types false`.
- No other change: the declarations, statements and proofs are the FLT text, including the closing
  `#guard_msgs in #print axioms` checks.

## Contents

Declarations, with their original FLT names, all in namespace `NeronModelInfra` (no new definitions or statements
are introduced). The file builds on the `SchemeHomOver`, `genericFibreRestrict` and `NeronModelPropertyBundle`
declarations of `Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier`.

- composition bookkeeping for `SchemeHomOver`: def `schemeHomOverId`, theorem `schemeHomOverId_coe`,
  def `schemeHomOverComp`, theorems `schemeHomOverComp_coe`, `schemeHomOverComp_assoc`,
  `schemeHomOverComp_id_left`, `schemeHomOverComp_id_right`
- functoriality of generic-fibre restriction: theorems `genericFibreRestrict_schemeHomOverId`,
  `genericFibreRestrict_schemeHomOverComp`, `genericFibreRestrict_endComp`
- extension of morphisms from the generic fibre: theorems `neronHomRestrict_bijective_of_smooth`,
  `neronEndRestrict_bijective_of_smooth`, `NeronModelPropertyBundle.homRestrict_bijective`,
  `NeronModelPropertyBundle.endRestrict_bijective`, `NeronModelPropertyBundle.existsUnique_endExtension`,
  `NeronModelPropertyBundle.exists_endExtension_hom`, `NeronModelPropertyBundle.endExtension_unique_hom`,
  `NeronModelPropertyBundle.integralPoints_bijective`
- def `NeronModelPropertyBundle.endExtensionEquiv` and theorems `NeronModelPropertyBundle.endExtensionEquiv_apply`,
  `NeronModelPropertyBundle.endExtensionEquiv_symm_restrict`, `NeronModelPropertyBundle.restrict_endExtensionEquiv_symm`,
  `NeronModelPropertyBundle.endExtensionEquiv_symm_id`, `NeronModelPropertyBundle.endExtensionEquiv_symm_comp`,
  `NeronModelPropertyBundle.endExtensionEquiv_symm_commute`, `NeronModelPropertyBundle.endExtensionEquiv_symm_involution`
- families: theorems `NeronModelPropertyBundle.existsUnique_familyExtension`,
  `NeronModelPropertyBundle.familyExtension_relation`
- FLT test instances ("gates") for the trivial group scheme over `ℤ_[p]` and `ℤ_[3]`: theorems
  `gate_endRestrict_bijective_trivialGroupScheme_zp`, `gate_endExtensionEquiv_symm_id_trivialGroupScheme_z3`,
  `gate_existsUnique_familyExtension_trivialGroupScheme_z3`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier`.
