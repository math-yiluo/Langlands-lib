import Langlands.Representation.Archimedean.PairBlockExponent

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

/-- Equality of the real pair-factor denominators against every singleton with real exponent
zero transfers every strict lower bound on the block exponents from one list to the other. -/
def RealPairFactorExponentComparisonStatement : Prop :=
  ∀ (xs ys : List RealBlock) (a : ℝ),
    (∀ y ∈ ys, a < realBlockExponent y) →
    (∀ z : RealBlock, realBlockExponent z = 0 →
      (realPairLFactor xs [z]).denominator = (realPairLFactor ys [z]).denominator) →
    ∀ x ∈ xs, a < realBlockExponent x

end Langlands.Archimedean
