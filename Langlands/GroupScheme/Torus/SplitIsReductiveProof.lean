import Langlands.GroupScheme.Torus.SplitReductiveStatement
import Langlands.GroupScheme.Torus.SplitReductiveProof

/-!
# Proof of `Langlands.GroupScheme.IsSplitTorus.IsReductiveStatement`

A named theorem for a statement that follows directly from published results.
-/

universe u

namespace Langlands.GroupScheme.IsSplitTorus

/-- Proof of `IsReductiveStatement`. -/
theorem isReductiveStatement : IsReductiveStatement.{u} :=
  reductiveStatement.2

end Langlands.GroupScheme.IsSplitTorus
