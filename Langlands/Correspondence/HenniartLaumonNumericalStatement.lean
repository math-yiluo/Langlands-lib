import Langlands.Correspondence.HenniartLocalNumerical
import Langlands.LocalField.LaurentSeries

namespace Langlands.Henniart

/-- Over a Laurent-series local field, increasing the rank by the positive Swan exponent
preserves the extended cardinality of the refined Weil stratum at each admissible torsion number. -/
def LaumonNumericalStatement.{uK, uW} : Prop :=
  ∀ (k : Type uK) [Field k] [Finite k] (d s f : ℕ),
    let X := LaurentSeries k
    letI := LocalField.Laurent.valuativeRel k
    let Ω := SeparableClosure X
    1 ≤ s → f ∣ Nat.gcd (d + 1) s →
      (LocalNumerical.weilRefinedStratum.{uK, uK, uW} X Ω d s f).encard =
        (LocalNumerical.weilRefinedStratum.{uK, uK, uW} X Ω (d + s) s f).encard

end Langlands.Henniart
