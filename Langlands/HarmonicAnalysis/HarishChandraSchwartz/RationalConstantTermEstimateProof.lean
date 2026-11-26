import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalConstantTermAnalyticReduction
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiGlobalUpperBoundProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalUnipotentWeightIntegrabilityProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviXiLowerBoundProof

/-! # Waldspurger II.4.5 on actual rational points -/

universe u

namespace Langlands.HarishChandraSchwartz

/-- Waldspurger's Proposition II.4.5 for the opposite standard parabolic, on
actual rational points: the normalized constant-term integral of `Ξ` against a
negative power of the height is bounded by `Ξ^{M_J}` times any prescribed
negative power of the height on the Levi. -/
theorem rationalConstantTermEstimate : RationalConstantTermEstimateStatement.{u} :=
  rationalConstantTermEstimate_of_analyticInputs.{u}
    rationalXiGlobalUpperBound.{u} rationalUnipotentWeightIntegrability.{u}
    rationalLeviXiLowerBound.{u}

end Langlands.HarishChandraSchwartz
