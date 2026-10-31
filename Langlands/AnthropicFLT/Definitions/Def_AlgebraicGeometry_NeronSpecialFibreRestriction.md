# `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronSpecialFibreRestriction`

## Source

Port of `Definitions/Def_AlgebraicGeometry_NeronSpecialFibreRestriction.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem
(commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2"). The text is the FLT text except for the changes listed below.
Licence: Apache License 2.0, Copyright 2026 Anthropic, PBC; unmodified copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice is recorded for it.
The Lean file starts with a notice recording the modification.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`,
  `backward.isDefEq.respectTransparency.types false`.
- No other change: the declarations, statements and proofs are the FLT text.

## Contents

Declarations, with their original FLT names, all in namespace `NeronSpecialFibreInfra` (no new definitions or
statements are introduced). The file restricts morphisms over a base `B` along a base change `C ⟶ B`
(`fibreRestrictAlong`), specialises this to the generic fibre and to the special fibre `Spec (R ⧸ m)`, and transfers
endomorphisms of a Néron model from the generic to the special fibre.

- bookkeeping: defs `homOverId`, `homOverComp`; theorems `homOverId_coe`, `homOverComp_coe`
- restriction along a base change: def `fibreRestrictAlong`; theorems `fibreRestrictAlong_coe_comp_fst`,
  `fibreRestrictAlong_coe_comp_snd`, `fibreRestrictAlong_coe_eq_pullbackMap`, `fibreRestrictAlong_homOverId`,
  `fibreRestrictAlong_homOverComp`
- generic fibre: theorems `fibreRestrictAlong_specGenericFibreInclusion`, `genericFibreRestrict_homOverId`,
  `genericFibreRestrict_homOverComp`
- special fibre: def `specClosedFibreInclusion`; theorems `specClosedFibreInclusion_eq`,
  `specClosedFibreInclusion_eq_spec_algebraMap`, `isClosedImmersion_specClosedFibreInclusion`, `isField_residueField`;
  def `specialFibreRestrict`; theorems `specialFibreRestrict_eq_fibreRestrictAlong`, `specialFibreRestrict_coe_comp_fst`,
  `specialFibreRestrict_coe_comp_snd`, `specialFibreRestrict_homOverId`, `specialFibreRestrict_homOverComp`
- Néron extension of endomorphisms: defs `neronEndRestrictEquiv`, `neronEndExtension`; theorems
  `neronEndRestrictEquiv_apply`, `genericFibreRestrict_neronEndExtension`, `neronEndExtension_eq_of_restrict`,
  `neronEndExtension_genericFibreRestrict`, `neronEndExtension_homOverId`, `neronEndExtension_homOverComp`
- transfer to the special fibre: def `neronSpecialFibreTransfer`; theorems `neronSpecialFibreTransfer_eq_of_restrict`,
  `specialFibreRestrict_congr_genericFibre`, `exists_neronExtension_specialFibreRestrict`,
  `neronSpecialFibreTransfer_homOverId`, `neronSpecialFibreTransfer_homOverComp`
- FLT test instances ("gates"): theorems `gate_specialFibreRestrict_id_trivialGroupScheme_zp`,
  `gate_specialFibreRestrict_id_trivialGroupScheme_z3`, `gate_neronSpecialFibreTransfer_id_trivialGroupScheme_z3`,
  `gate_isClosedImmersion_specClosedFibreInclusion_z3`, `gate_isField_residueField_z3`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier`.
