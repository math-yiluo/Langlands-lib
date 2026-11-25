# Integral closures of a complete DVR in a finite separable extension

Let `K` be a field with a complete discrete valuation, given as NYLL's bundle
`ValuationTheory.DiscreteValuationField.CompleteDVF` (`base`), and let `L` be a
finite separable extension of `K`. The two theorems in
`Langlands.CommutativeAlgebra.FiniteIntegralClosure` concern the actual integral
closure `integralClosure base.valuationSubring L` of the valuation ring of `K`:

- `integralClosure_isDiscreteValuationRing_of_finite_separable`: it is a
  discrete valuation ring (NYLL M245.011);
- `integralClosure_maximalIdeal_isAdicComplete_of_finite_separable`: it is
  adically complete for its canonical maximal ideal
  `ValuedExtension.CanonicalIntegralClosure.maximalIdeal (L := L) base`
  (NYLL M245.014).

Each proof is the theorem of the same name in
`ValuationTheory.DiscreteValuationField.ValuedExtension`, from
`Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure`,
which has the same hypotheses and conclusion with `K` and `L` implicit. Here `K`
and `L` are explicit, as in the corresponding statements of the Library's port
of NYLL, so callers keep the positional application `K L base`. The universes
of `K`, of the value group of `base` and of `L` are independent. [Lean source](FiniteIntegralClosure.lean)

They are used by [the finite separable extensions of a complete DVR](DvrFiniteSeparableExtension.md).
