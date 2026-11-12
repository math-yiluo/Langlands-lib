import Langlands.GroupScheme.Torus.SplitReductiveStatement
import Langlands.GroupScheme.Torus.SplitReductiveProof

/-!
# Proof of `Langlands.GroupScheme.IsSplitTorus.IsConnectedReductiveStatement`

A named theorem for a statement that follows directly from published results.
-/

universe u

namespace Langlands.GroupScheme.IsSplitTorus

/-- Proof of `IsConnectedReductiveStatement`. -/
theorem isConnectedReductiveStatement : IsConnectedReductiveStatement.{u} :=
  reductiveStatement.1

end Langlands.GroupScheme.IsSplitTorus
