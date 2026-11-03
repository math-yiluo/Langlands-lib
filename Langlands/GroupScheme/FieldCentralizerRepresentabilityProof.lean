import Langlands.AlgebraicGeometry.ClosedFactorizationLocusProof
import Langlands.GroupScheme.FixedRepresentabilityReduction

/-! # Closed field centralizers of affine commutative groups -/

universe u

namespace Langlands.GroupScheme

/-- The exact published closed-representability target. -/
theorem fieldCentralizerRepresentability : FieldCentralizerRepresentabilityStatement.{u} :=
  fieldCentralizerRepresentability_of_closedFactorizationLocus
    Langlands.AlgebraicGeometry.ClosedFactorizationLocusProof.closedFactorizationLocus

end Langlands.GroupScheme
