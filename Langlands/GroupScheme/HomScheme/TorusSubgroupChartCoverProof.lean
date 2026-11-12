import Langlands.GroupScheme.HomScheme.TorusSubgroupChartCoverReductionProof
import Langlands.GroupScheme.HomScheme.SmoothTorusSubgroupRepresentabilityProof

/-! # Chart covers of closed torus subgroups over every base -/

universe u

namespace Langlands.GroupScheme.TorusSubgroupModuli

/-- Chart covers of closed torus subgroups over every base, with all structural inputs discharged. -/
theorem chartCover : ChartCoverStatement.{u} :=
  chartCoverReduction.{u} finiteTypeChartCover.{u}

end Langlands.GroupScheme.TorusSubgroupModuli
