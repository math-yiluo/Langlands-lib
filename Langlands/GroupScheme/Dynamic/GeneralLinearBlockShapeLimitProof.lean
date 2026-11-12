import Langlands.GroupScheme.Dynamic.GeneralLinearStatement
import Langlands.GroupScheme.Dynamic.GeneralLinearProof

/-!
# Proof of `Langlands.GroupScheme.GeneralLinear.BlockShapeLimitStatement`

A named theorem for a statement that follows directly from published results.
-/

universe u

namespace Langlands.GroupScheme.GeneralLinear

/-- Proof of `BlockShapeLimitStatement`. -/
theorem blockShapeLimit : BlockShapeLimitStatement.{u} :=
  dynamicStatement.2.2.2.2

end Langlands.GroupScheme.GeneralLinear
