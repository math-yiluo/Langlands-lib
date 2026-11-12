import Langlands.GroupScheme.RelativeIdentityComponentStatements
import Langlands.GroupScheme.RelativeIdentityComponent.SmoothProof

/-!
# Proof of `Langlands.GroupScheme.RelativeIdentityComponent.SmoothNormalityStatement`

A named theorem for a statement that follows directly from published results.
-/

universe u

namespace Langlands.GroupScheme.RelativeIdentityComponent

/-- Proof of `SmoothNormalityStatement`. -/
theorem smoothNormality : SmoothNormalityStatement.{u} :=
  smoothStructure.2.1

end Langlands.GroupScheme.RelativeIdentityComponent
