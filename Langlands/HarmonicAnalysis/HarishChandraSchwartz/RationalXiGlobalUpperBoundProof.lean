import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiUpperBoundProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCartanIwasawaWeightComparisonProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiGlobalUpperBoundReduction

/-! # The global Iwasawa-weight upper bound for actual Xi -/

universe u

namespace Langlands.HarishChandraSchwartz

/-- The actual Xi function is bounded by its Iwasawa weight times a polynomial
in the height, uniformly over all rational points. -/
theorem rationalXiGlobalUpperBound : RationalXiGlobalUpperBoundStatement.{u} :=
  rationalXiGlobalUpperBound_of_chamber_of_comparison.{u}
    rationalXiUpperBound.{u} rationalCartanIwasawaWeightComparison.{u}

end Langlands.HarishChandraSchwartz
