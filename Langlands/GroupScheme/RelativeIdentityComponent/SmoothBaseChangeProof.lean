import Langlands.GroupScheme.RelativeIdentityComponentStatements
import Langlands.GroupScheme.RelativeIdentityComponent.SmoothProof

/-!
# Proof of `Langlands.GroupScheme.RelativeIdentityComponent.SmoothBaseChangeStatement`

A named theorem for a statement that follows directly from published results.
-/

universe u

namespace Langlands.GroupScheme.RelativeIdentityComponent

/-- Proof of `SmoothBaseChangeStatement`. -/
theorem smoothBaseChange : SmoothBaseChangeStatement.{u} :=
  smoothStructure.2.2

end Langlands.GroupScheme.RelativeIdentityComponent
