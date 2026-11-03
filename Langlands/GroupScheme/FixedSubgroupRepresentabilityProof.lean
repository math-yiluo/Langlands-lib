import Langlands.AlgebraicGeometry.ClosedFactorizationLocusProof
import Langlands.GroupScheme.FixedRepresentabilityReduction

/-! # Closed representability of fixed subgroups -/

universe u

namespace Langlands.GroupScheme

/-- The exact published closed-representability target. -/
theorem fixedSubgroupRepresentability : FixedSubgroupRepresentabilityStatement.{u} :=
  fixedSubgroupRepresentability_of_closedFactorizationLocus
    Langlands.AlgebraicGeometry.ClosedFactorizationLocusProof.closedFactorizationLocus

end Langlands.GroupScheme
