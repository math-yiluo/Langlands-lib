# `Langlands.AnthropicFLT.Definitions.Def_JacJ1_ChartAlgebra`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Definition module (FLT `Definitions/`).

## Source and licence

Port of `Definitions/Def_JacJ1_ChartAlgebra.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Affine charts of the smooth model of a function field (namespace `AlgebraicCurve.CurveModel`),
for a field extension `L / K`.

- `aevalAdjoin K s : K[X] →ₐ[K] K[s]` (surjective, `aevalAdjoin_surjective`); scoped instances: `K[s]`
  is a principal ideal ring and a Dedekind domain.
- `chartRing K S`: the subalgebra of `L` of elements integral over `K[S]` (`mem_chartRing_iff`), with
  `adjoin_le_chartRing`, `subset_chartRing`, monotonicity `chartRing_mono`, the inclusions
  `chartIncl` (`coe_chartIncl`, `chartIncl_injective`), and instances: `K[S]`-algebra structure,
  scalar towers, and `IsIntegralClosure (chartRing K S) K[S] L`.
- Section `OneGenerator` (characteristic zero, `L` finite over `K(s)`): scoped instances
  `charZero_adjoin_simple`, `isSeparable_adjoin_simple`; instances: `chartRing K {s}` is a Dedekind
  domain, finite over `K[s]`, has fraction field `L`, is of finite type over `K` and noetherian.
- Section `Valuation`: for a valuation subring `O` of `L` containing `K`, `K[S] ⊆ O` and
  `chartRing K S ⊆ O` when `S ⊆ O` (`adjoin_le_valuationSubring`, `chartRing_le_valuationSubring`;
  `ValuationSubring.toSubalgebraOfBase` and its lemmas); the centre `centre K s O` (elements of
  valuation `< 1`), a prime ideal (`centre_isPrime`), nonzero for `O ≠ L` (`centre_ne_bot`);
  `primeOfValuationSubring` (the height-one prime) whose valuation subring is `O`
  (`valuationSubringAtPrime_le`, `valuationSubringAtPrime_primeOfValuationSubring`);
  `chartPlaces K s` (the places at which `s` is integral, with `mem_chartPlaces_iff` and
  `mem_chartPlaces_or_mem_chartPlaces_inv`); `exists_ofHeightOneSpectrum_eq`,
  `mem_ofHeightOneSpectrum`, `ofHeightOneSpectrum_injective`, and the bijection
  `primeEquivChartPlaces K s` between height-one primes of `chartRing K {s}` and `chartPlaces K s`.
- Section `InvertGenerator`: for `s ∈ S`, `s ≠ 0`, every element `x` of `K[S ∪ {s⁻¹}]`, respectively of
  `chartRing K (S ∪ {s⁻¹})`, satisfies `sⁿ x ∈ K[S]`, respectively `sⁿ x ∈ chartRing K S`, for some
  `n` (`exists_pow_mul_mem_adjoin`, `exists_pow_mul_mem_chartRing`).

## Declarations

Names, namespaces and statements are the FLT ones.

- def `AlgebraicCurve.CurveModel.aevalAdjoin`
- theorem `AlgebraicCurve.CurveModel.aevalAdjoin_surjective`
- scoped instance `AlgebraicCurve.CurveModel.isPrincipalIdealRing_adjoin_singleton`
- scoped instance `AlgebraicCurve.CurveModel.isDedekindDomain_adjoin_singleton`
- def `AlgebraicCurve.CurveModel.chartRing`
- theorem `AlgebraicCurve.CurveModel.mem_chartRing_iff`
- theorem `AlgebraicCurve.CurveModel.adjoin_le_chartRing`
- theorem `AlgebraicCurve.CurveModel.subset_chartRing`
- theorem `AlgebraicCurve.CurveModel.chartRing_mono`
- abbrev `AlgebraicCurve.CurveModel.chartIncl`
- theorem `AlgebraicCurve.CurveModel.coe_chartIncl`
- theorem `AlgebraicCurve.CurveModel.chartIncl_injective`
- instance `AlgebraicCurve.CurveModel.algebraAdjoin`
- instance `AlgebraicCurve.CurveModel.isScalarTower_adjoin`
- instance `AlgebraicCurve.CurveModel.isScalarTower_base_adjoin`
- instance `AlgebraicCurve.CurveModel.isIntegralClosure`
- scoped instance `AlgebraicCurve.CurveModel.charZero_adjoin_simple`
- scoped instance `AlgebraicCurve.CurveModel.isSeparable_adjoin_simple`
- instance `AlgebraicCurve.CurveModel.isDedekindDomain_chartRing`
- instance `AlgebraicCurve.CurveModel.finite_chartRing`
- instance `AlgebraicCurve.CurveModel.isFractionRing_chartRing`
- instance `AlgebraicCurve.CurveModel.finiteType_chartRing`
- instance `AlgebraicCurve.CurveModel.isNoetherianRing_chartRing`
- theorem `AlgebraicCurve.CurveModel.adjoin_le_valuationSubring`
- def `ValuationSubring.toSubalgebraOfBase`
- theorem `ValuationSubring.mem_toSubalgebraOfBase_iff`
- theorem `ValuationSubring.integers_toSubalgebraOfBase`
- theorem `AlgebraicCurve.CurveModel.chartRing_le_valuationSubring`
- def `AlgebraicCurve.CurveModel.centre`
- theorem `AlgebraicCurve.CurveModel.mem_centre_iff`
- theorem `AlgebraicCurve.CurveModel.valuation_coe_le_one`
- theorem `AlgebraicCurve.CurveModel.valuation_eq_one_of_not_mem_centre`
- instance `AlgebraicCurve.CurveModel.centre_isPrime`
- def `AlgebraicCurve.CurveModel.chartPlaces`
- theorem `AlgebraicCurve.CurveModel.mem_chartPlaces_iff`
- theorem `AlgebraicCurve.CurveModel.mem_chartPlaces_or_mem_chartPlaces_inv`
- theorem `AlgebraicCurve.CurveModel.centre_ne_bot`
- def `AlgebraicCurve.CurveModel.primeOfValuationSubring`
- theorem `AlgebraicCurve.CurveModel.valuationSubringAtPrime_le`
- theorem `AlgebraicCurve.CurveModel.valuationSubringAtPrime_primeOfValuationSubring`
- theorem `AlgebraicCurve.CurveModel.exists_ofHeightOneSpectrum_eq`
- theorem `AlgebraicCurve.CurveModel.mem_ofHeightOneSpectrum`
- theorem `AlgebraicCurve.CurveModel.ofHeightOneSpectrum_injective`
- def `AlgebraicCurve.CurveModel.primeEquivChartPlaces`
- theorem `AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces`
- theorem `AlgebraicCurve.CurveModel.exists_pow_mul_mem_adjoin`
- theorem `AlgebraicCurve.CurveModel.exists_pow_mul_mem_chartRing`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup` (same contribution).
Other imports: `Mathlib.RingTheory.DedekindDomain.IntegralClosure`, `Mathlib.RingTheory.DedekindDomain.AdicValuation`, `Mathlib.RingTheory.Localization.Integral`, `Mathlib.RingTheory.Valuation.Integral`, `Mathlib.RingTheory.Polynomial.ScaleRoots`, `Mathlib.Algebra.Polynomial.Lifts`, `Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra`, `Mathlib.RingTheory.Adjoin.Polynomial.Basic`, `Mathlib.RingTheory.Algebraic.Basic`, `Mathlib.FieldTheory.Perfect`.
