import Langlands.GroupScheme.Dynamic.GeneralLinearStatement
import Langlands.GroupScheme.Dynamic.GeneralLinearProof

/-!
# Proof of `Langlands.GroupScheme.GeneralLinear.BlockShapeDynamicStatement`

A named theorem for a statement that follows directly from published results.
-/

universe u

namespace Langlands.GroupScheme.GeneralLinear

/-- Proof of `BlockShapeDynamicStatement`. -/
theorem blockShapeDynamic : BlockShapeDynamicStatement.{u} :=
  dynamicStatement.2.1

end Langlands.GroupScheme.GeneralLinear
