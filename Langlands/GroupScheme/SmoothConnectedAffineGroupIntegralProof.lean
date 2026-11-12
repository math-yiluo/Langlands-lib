import Langlands.GroupScheme.SmoothConnectedGeometryStatement
import Langlands.GroupScheme.SmoothConnectedGeometryProof

/-!
# Proof of `Langlands.GroupScheme.SmoothConnectedAffineGroupIntegralStatement`

A named theorem for a statement that follows directly from published results.
-/

universe u

namespace Langlands.GroupScheme

/-- Proof of `SmoothConnectedAffineGroupIntegralStatement`. -/
theorem smoothConnectedAffineGroupIntegral : SmoothConnectedAffineGroupIntegralStatement.{u} :=
  smoothConnectedAffineGeometry.1

end Langlands.GroupScheme
