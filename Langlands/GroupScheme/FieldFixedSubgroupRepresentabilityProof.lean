import Langlands.AlgebraicGeometry.ClosedFactorizationLocusProof
import Langlands.GroupScheme.FixedRepresentabilityReduction

/-! # Closed fixed subgroups over a field -/

universe u

namespace Langlands.GroupScheme

/-- The exact published closed-representability target. -/
theorem fieldFixedSubgroupRepresentability : FieldFixedSubgroupRepresentabilityStatement.{u} :=
  fieldFixedSubgroupRepresentability_of_closedFactorizationLocus
    Langlands.AlgebraicGeometry.ClosedFactorizationLocusProof.closedFactorizationLocus

end Langlands.GroupScheme
