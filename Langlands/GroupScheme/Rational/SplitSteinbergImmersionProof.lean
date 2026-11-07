import Langlands.GroupScheme.Rational.SteinbergIndependentWeightReduction
import Langlands.GroupScheme.Rational.IndependentWeightProductProof

/-! # Closed immersion of the actual split Steinberg root product -/

universe u

namespace Langlands.GroupScheme

/-- The supplied split Steinberg root product is a closed immersion over every field. -/
theorem splitSteinbergImmersion : SplitSteinbergImmersionStatement.{u} :=
  splitSteinbergImmersion_of_independentWeightProduct independentWeightProductImmersion

end Langlands.GroupScheme
