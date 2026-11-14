import Langlands.GroupScheme.RelativeLevi.BorelLocusReduction
import Langlands.GroupScheme.RelativeLevi.SplitMaximalTorusChartProof

/-! # The Borel locus of a relative parabolic is open and closed -/

universe u

namespace Langlands.GroupScheme

/-- The Borel locus of a relative parabolic subgroup of a reductive group
scheme is open and closed, over every base scheme. -/
theorem relativeBorelLocusClopen : RelativeBorelLocusClopenStatement.{u} :=
  relativeBorelLocusClopen_of_splitMaximalTorusCharts
    relativeParabolicSplitMaximalTorusCharts

end Langlands.GroupScheme
