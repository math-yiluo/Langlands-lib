import Langlands.GroupScheme.Dynamic.GeneralLinearStatement
import Langlands.GroupScheme.Dynamic.GeneralLinearProof

/-!
# Proof of `Langlands.GroupScheme.GeneralLinear.DiagonalCocharacterDynamicStatement`

A named theorem for a statement that follows directly from published results.
-/

universe u

namespace Langlands.GroupScheme.GeneralLinear

/-- Proof of `DiagonalCocharacterDynamicStatement`. -/
theorem diagonalCocharacterDynamic : DiagonalCocharacterDynamicStatement.{u} :=
  dynamicStatement.1

end Langlands.GroupScheme.GeneralLinear
