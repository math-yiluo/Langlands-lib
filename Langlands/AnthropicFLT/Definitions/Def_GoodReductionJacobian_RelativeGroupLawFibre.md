# `Langlands.AnthropicFLT.Definitions.Def_GoodReductionJacobian_RelativeGroupLawFibre`

## Source

Port of `Definitions/Def_GoodReductionJacobian_RelativeGroupLawFibre.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem
(commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2"). The text is the FLT text except for the changes listed below.
Licence: Apache License 2.0, Copyright 2026 Anthropic, PBC; unmodified copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice is recorded for it.
The Lean file starts with a notice recording the modification.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports
  (`Mathlib.AlgebraicGeometry.ResidueField`, `Mathlib.AlgebraicGeometry.Pullbacks`) are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`,
  `backward.isDefEq.respectTransparency.types false`.
- No other change: the declarations, statements and proofs are the FLT text.

## Contents

Declarations, with their original FLT names, all in namespace `GoodReductionJacobian.RelativeGroupLaw` (no new
definitions or statements are introduced). For `f : A ⟶ Spec R` and a point `s` of `Spec R`, the file defines the
fibre of `f` over `s` as the pullback along `fromSpecResidueField s`, identifies its points with points of `A`
over the composite base, and restricts a `RelativeGroupLaw R f` to a `RelativeGroupLaw` of the fibre.

- abbrevs `baseResidueField`, `basePointInclusion`, `fibreScheme`, `fibreStr`
- theorems `fibreScheme_eq_fiber`, `fibreStr_eq_fiberToSpecResidueField` (comparison with Mathlib's
  `Scheme.Hom.fiber` and `Scheme.Hom.fiberToSpecResidueField`)
- defs `fibrePointToBase`, `fibrePointOfBase`, `fibrePointEquiv`; theorems `fibrePointToBase_coe`,
  `fibrePointOfBase_coe`, `fibrePointToBase_ofBase`, `fibrePointOfBase_toBase`, `fibrePointToBase_schemeHomOverComp`
- def `fibre` (the restricted group law); theorems `fibre_mul`, `fibre_one`, `fibre_inv`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel`.
