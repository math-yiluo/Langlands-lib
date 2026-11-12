import Langlands.GroupScheme.RelativeIdentityComponentStatements
import Langlands.GroupScheme.RelativeIdentityComponent.SmoothProof

/-!
# Proof of `Langlands.GroupScheme.RelativeIdentityComponent.SmoothExistenceStatement`

A named theorem for a statement that follows directly from published results.
-/

universe u

namespace Langlands.GroupScheme.RelativeIdentityComponent

/-- Proof of `SmoothExistenceStatement`. -/
theorem smoothExistence : SmoothExistenceStatement.{u} :=
  smoothStructure.1

end Langlands.GroupScheme.RelativeIdentityComponent
