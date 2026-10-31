# `Langlands.AnthropicFLT.Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange`

## Source

Port of `Definitions/Def_GoodReductionJacobian_RelativeGroupLawBaseChange.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem
(commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2"). The text is the FLT text except for the changes listed below.
Licence: Apache License 2.0, Copyright 2026 Anthropic, PBC; unmodified copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice is recorded for it.
The Lean file starts with a notice recording the modification.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`) are renamed to `Langlands.AnthropicFLT.*`; the Mathlib import
  `Mathlib.AlgebraicGeometry.Pullbacks` is unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`,
  `backward.isDefEq.respectTransparency.types false`.
- No other change: the declarations, statements and proofs are the FLT text.

## Contents

Declarations, with their original FLT names, all in namespace `GoodReductionJacobian.RelativeGroupLaw` (no new
definitions or statements are introduced). For `ι : Spec R' ⟶ Spec R` and `f : A ⟶ Spec R`, the base change of `f`
is `pullback.snd f ι`; its points over `t'` correspond to points of `A` over `t' ≫ ι`, and a `RelativeGroupLaw R f`
induces a `RelativeGroupLaw R'` on the base change by transporting the operations along this correspondence.

- abbrevs `baseChangeScheme`, `baseChangeStr`
- defs `baseChangePointToBase`, `baseChangePointOfBase`, `baseChangePointEquiv`; theorems `baseChangePointToBase_coe`,
  `baseChangePointOfBase_coe`, `baseChangePointToBase_ofBase`, `baseChangePointOfBase_toBase`,
  `baseChangePointToBase_schemeHomOverComp`, `baseChangePointToBase_comp_fibreRestrictAlong`
- def `baseChange`; theorems `baseChange_mul`, `baseChange_one`, `baseChange_inv`, `baseChangePointToBase_mul`,
  `baseChangePointToBase_one`, `baseChangePointToBase_inv`, `IsCommutative.baseChange`, `fibre_eq_baseChange`
- generic fibre: abbrevs `genericFibreScheme`, `genericFibreStr`, `genericFibre`; theorem
  `baseChangePointToBase_comp_genericFibreRestrict`

The bridge `Langlands.AbelianScheme.GroupSchemeSubalgebraDescentProof` uses `baseChange_mul`,
`baseChangePointOfBase_coe` and `baseChangePointToBase` to compare this group law with the group law of
`Over.pullback`.

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel`,
`Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension`,
`Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronSpecialFibreRestriction`,
`Langlands.AnthropicFLT.Definitions.Def_GoodReductionJacobian_RelativeGroupLawFibre`.
