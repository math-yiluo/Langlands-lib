import Langlands.GroupScheme.Reductive.GeneralLinearStatement
import Langlands.GroupScheme.Reductive.GeneralLinearProof

/-!
# Proof of `Langlands.GroupScheme.GeneralLinear.IsConnectedReductiveStatement`

A named theorem for a statement that follows directly from published results.
-/

universe u

namespace Langlands.GroupScheme.GeneralLinear

/-- Proof of `IsConnectedReductiveStatement`. -/
theorem isConnectedReductiveStatement : IsConnectedReductiveStatement.{u} :=
  reductiveStatement.1

end Langlands.GroupScheme.GeneralLinear
