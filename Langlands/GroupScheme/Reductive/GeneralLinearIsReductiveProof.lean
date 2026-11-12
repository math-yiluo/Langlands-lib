import Langlands.GroupScheme.Reductive.GeneralLinearStatement
import Langlands.GroupScheme.Reductive.GeneralLinearProof

/-!
# Proof of `Langlands.GroupScheme.GeneralLinear.IsReductiveStatement`

A named theorem for a statement that follows directly from published results.
-/

universe u

namespace Langlands.GroupScheme.GeneralLinear

/-- Proof of `IsReductiveStatement`. -/
theorem isReductiveStatement : IsReductiveStatement.{u} :=
  reductiveStatement.2

end Langlands.GroupScheme.GeneralLinear
