import Langlands.GroupScheme.Absolute.RankOneAlgebraicClosureReduction
import Langlands.GroupScheme.Reductive.RankOneBorelDynamicProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Absolute.CentralizerBorelIntersectionProof

/-! # rankOneAlgClosedBorelExclusion: unconditional proof from published reductions -/

universe u

namespace Langlands.GroupScheme

/-- Over an algebraically closed field, a Borel subgroup containing the specified split maximal torus of a connected reductive group has no pair of nonzero actual Lie-image witnesses of opposite root weights. -/
theorem rankOneAlgClosedBorelExclusion :
    RankOneAlgClosedBorelExclusionStatement.{u} :=
  rankOneAlgClosedBorelExclusion_of_geometricStatements rankOneBorelDynamic
    dynamicCentralizerReductive centralizerBorelIntersection

end Langlands.GroupScheme
