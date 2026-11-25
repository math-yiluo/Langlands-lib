# Completeness from a positive ideal power, with explicit ring and module

`Langlands.CommutativeAlgebra.AdicCompleteness.isAdicComplete_of_isAdicComplete_pow`
states that a module `M` over a commutative ring `R` that is adically complete
for `I ^ n`, with `0 < n`, is adically complete for the ideal `I`. The ring and
module are explicit arguments and lie in independent universes. [Lean source](AdicCompleteness.lean)

The proof is NYLL's theorem
`ValuationTheory.DiscreteValuationField.isAdicComplete_of_isAdicComplete_pow`
(NYLL M105.013), from `Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.AdicPower`.
That theorem has the same hypotheses and conclusion, with `R` and `M` implicit.
The binders here are those of
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.IsAdicCompleteOfIsAdicCompletePowStatement`
in the Library's port of NYLL, so callers keep the positional application
`R M I hn`. The theorem has its own namespace because the port module
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.AdicPowerCompletenessProof`,
which declares the port's name, remains in the Library.

It is used by [the finite extensions of the complete DVR base](../AlgebraicGeometry/DvrAffineReducedFibre/FiniteDvrExtension.md).
