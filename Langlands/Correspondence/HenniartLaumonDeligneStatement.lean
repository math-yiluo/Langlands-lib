import Langlands.Correspondence.HenniartRefinedStrata

namespace Langlands.Henniart

/-- Input (I2) of the numerical local Langlands route. At Swan exponent
`1 ≤ s < d * e`, the torsion-number-one Weil orbit counts in ranks `d` and
`d + s` agree, where `e` is the absolute ramification index. -/
def LaumonDeligneCountStatement.{uK, uW} : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (k s : ℕ),
    1 ≤ s → s < (k + 1) * K.canonicalTopologicalData.ramificationIndex →
      Numerical.weilTwistIrreducibleCount.{uK, uW} K k s =
        Numerical.weilTwistIrreducibleCount.{uK, uW} K (k + s) s

end Langlands.Henniart
