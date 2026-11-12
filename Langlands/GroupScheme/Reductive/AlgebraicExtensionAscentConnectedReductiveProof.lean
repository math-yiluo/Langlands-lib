import Langlands.GroupScheme.Reductive.AlgebraicExtensionAscentStatement
import Langlands.GroupScheme.Reductive.AlgebraicExtensionAscent

/-!
# Proof of `Langlands.GroupScheme.ConnectedReductiveAlgebraicExtensionAscentStatement`

A named theorem for a statement that follows directly from published results.
-/

universe u

namespace Langlands.GroupScheme

/-- Proof of `ConnectedReductiveAlgebraicExtensionAscentStatement`. -/
theorem connectedReductiveAlgebraicExtensionAscent : ConnectedReductiveAlgebraicExtensionAscentStatement.{u} :=
  algebraicExtensionAscent.1

end Langlands.GroupScheme
