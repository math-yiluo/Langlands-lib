# `Langlands.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModelSmooth`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Definition module (FLT `Definitions/`).

## Source and licence

Port of `Definitions/Def_AlgebraicCurve_CurveModelSmooth.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- Manual edit for Mathlib drift (FLT line 250, line 262 here): `IsScalarTower.of_algebraMap_eq fun a => by` is replaced by `IsScalarTower.of_algebraMap_eq (S := Localization.Away t) fun a => by`. With the project's Mathlib the middle ring of `IsScalarTower.of_algebraMap_eq` is no longer inferred from the expected type `IsScalarTower K (Localization.Away t) L` before the proof term is elaborated (it was taken to be `L`); it is given by name, `(S := Localization.Away t)`, which states the same scalar tower.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

Smoothness of the affine charts of curve models in characteristic zero (namespace
`AlgebraicCurve.CurveModel`).

- `freeSubmersivePresentation R ι`: the submersive presentation of `MvPolynomial ι R` with no
  relations; the scoped instance `isStandardSmoothOfRelativeDimension_polynomial`: `R[X]` is standard
  smooth of relative dimension `1` over `R`; `smoothOfRelativeDimension_one_Spec_polynomial`:
  `Spec K[X] ⟶ Spec K` is smooth of relative dimension `1`.
- Section `Coordinate`: in a Dedekind domain, a nonzero prime `𝔪` contains an element `u ≠ 0`
  generating the maximal ideal of the localization at `𝔪` (`exists_mem_and_maximalIdeal_eq_span`);
  a nonzero element of a proper ideal of a `K`-algebra domain is transcendental over `K`
  (`transcendental_of_mem`).
- For a function field `L / K` of characteristic zero and a transcendental `s ∈ L` with `L` finite
  over `K(s)`, the chart ring `chartRing K {s}` (integral closure of `K[s]` in `L`, from
  `Def_JacJ1_ChartAlgebra`): it is finitely presented (`chartRing_finitePresentation`), formally
  smooth at the localizations at nonzero primes (étale over `K[X]` via a uniformizer,
  `formallySmooth_chartRing_localization_closed`) and at `0` (`…_bot`), so smooth at every prime
  (`chartRing_isSmoothAt`) and formally smooth (`formallySmooth_chartRing`).
- Kähler differentials: `isStandardSmoothOfRelativeDimension_adjoin_single`,
  `rank_kaehler_eq_of_formallyEtale`, `rank_kaehler_intermediateField_adjoin_single`,
  `rank_kaehler_eq_one_of_finite_adjoin` (`Ω_{L/K}` has rank `1`) and
  `rank_kaehler_chartRing_localization_away_eq_one`.
- Conclusions: `locally_isStandardSmoothOfRelativeDimension_one_chartRing` and
  `smoothOfRelativeDimension_one_Spec_chartRing`: `Spec (chartRing K {s}) ⟶ Spec K` is smooth of
  relative dimension `1`.

## Declarations

Names, namespaces and statements are the FLT ones.

- def `AlgebraicCurve.CurveModel.freeSubmersivePresentation`
- scoped instance `AlgebraicCurve.CurveModel.isStandardSmoothOfRelativeDimension_polynomial`
- theorem `AlgebraicCurve.CurveModel.smoothOfRelativeDimension_one_Spec_polynomial`
- theorem `AlgebraicCurve.CurveModel.exists_mem_and_maximalIdeal_eq_span`
- theorem `AlgebraicCurve.CurveModel.transcendental_of_mem`
- instance `AlgebraicCurve.CurveModel.chartRing_finitePresentation`
- theorem `AlgebraicCurve.CurveModel.formallySmooth_chartRing_localization_closed`
- theorem `AlgebraicCurve.CurveModel.formallySmooth_chartRing_localization_bot`
- theorem `AlgebraicCurve.CurveModel.chartRing_isSmoothAt`
- theorem `AlgebraicCurve.CurveModel.isStandardSmoothOfRelativeDimension_adjoin_single`
- theorem `AlgebraicCurve.CurveModel.rank_kaehler_eq_of_formallyEtale`
- theorem `AlgebraicCurve.CurveModel.rank_kaehler_intermediateField_adjoin_single`
- theorem `AlgebraicCurve.CurveModel.rank_kaehler_eq_one_of_finite_adjoin`
- theorem `AlgebraicCurve.CurveModel.rank_kaehler_chartRing_localization_away_eq_one`
- theorem `AlgebraicCurve.CurveModel.formallySmooth_chartRing`
- theorem `AlgebraicCurve.CurveModel.locally_isStandardSmoothOfRelativeDimension_one_chartRing`
- theorem `AlgebraicCurve.CurveModel.smoothOfRelativeDimension_one_Spec_chartRing`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModel` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_JacJ1_ChartAlgebra` (same contribution).
Other imports: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `Mathlib.AlgebraicGeometry.Morphisms.Etale`, `Mathlib.RingTheory.Extension.Presentation.Submersive`, `Mathlib.RingTheory.Smooth.StandardSmoothOfFree`, `Mathlib.RingTheory.Smooth.StandardSmoothCotangent`, `Mathlib.RingTheory.Smooth.Field`, `Mathlib.RingTheory.Smooth.Locus`, `Mathlib.RingTheory.RingHom.LocallyStandardSmooth`, `Mathlib.RingTheory.Etale.Kaehler`, `Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra`, `Mathlib.RingTheory.AlgebraicIndependent.Transcendental`, `Mathlib.RingTheory.Smooth.Fiber`, `Mathlib.RingTheory.Unramified.LocalRing`, `Mathlib.RingTheory.LocalRing.ResidueField.Instances`, `Mathlib.RingTheory.DedekindDomain.Dvr`, `Mathlib.RingTheory.Flat.TorsionFree`.
