import Langlands.GroupScheme.Reductive.RankOnePositiveRootBaseChange
import Langlands.GroupScheme.Reductive.RankOnePositiveRootProof

/-! # rankOneAlgClosedPositiveRootUniqueness: unconditional proof from published reductions -/

universe u

namespace Langlands.GroupScheme

/-- Over an algebraically closed field, the pairwise integral dependence hypothesis on actual roots of the specified split maximal torus implies uniqueness of a root positive on any specified cocharacter. -/
theorem rankOneAlgClosedPositiveRootUniqueness :
    RankOneAlgClosedPositiveRootUniquenessStatement.{u} :=
  rankOneAlgClosedPositiveRootUniqueness_of_statement rankOnePositiveRootUniqueness

end Langlands.GroupScheme
