import Langlands.Representation.RankinSelberg.RationalZeta

/-!
The algebraic normalization implication for a Laurent span with a common
denominator that contains one. This module states the implication only.
-/

namespace Langlands.RankinSelberg

/-- A common denominator and membership of one in the Laurent span suffice
for the existence of a normalized reciprocal-polynomial generator. -/
def NormalizedGeneratorExistenceStatement : Prop :=
  ∀ values : Set RationalFunctions,
    HasCommonDenominator values →
    (1 : RationalFunctions) ∈ zetaSpan values →
    NormalizedGeneratorExists values

end Langlands.RankinSelberg
