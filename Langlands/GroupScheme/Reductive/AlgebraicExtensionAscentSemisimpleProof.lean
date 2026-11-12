import Langlands.GroupScheme.Reductive.AlgebraicExtensionAscentStatement
import Langlands.GroupScheme.Reductive.AlgebraicExtensionAscent

/-!
# Proof of `Langlands.GroupScheme.SemisimpleAlgebraicExtensionAscentStatement`

A named theorem for a statement that follows directly from published results.
-/

universe u

namespace Langlands.GroupScheme

/-- Proof of `SemisimpleAlgebraicExtensionAscentStatement`. -/
theorem semisimpleAlgebraicExtensionAscent : SemisimpleAlgebraicExtensionAscentStatement.{u} :=
  algebraicExtensionAscent.2

end Langlands.GroupScheme
