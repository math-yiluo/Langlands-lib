import Langlands.GroupScheme.SmoothConnectedGeometryStatement
import Langlands.GroupScheme.SmoothConnectedGeometryProof

/-!
# Proof of `Langlands.GroupScheme.SmoothConnectedAffineProductIntegralStatement`

A named theorem for a statement that follows directly from published results.
-/

universe u

namespace Langlands.GroupScheme

/-- Proof of `SmoothConnectedAffineProductIntegralStatement`. -/
theorem smoothConnectedAffineProductIntegral : SmoothConnectedAffineProductIntegralStatement.{u} :=
  smoothConnectedAffineGeometry.2

end Langlands.GroupScheme
