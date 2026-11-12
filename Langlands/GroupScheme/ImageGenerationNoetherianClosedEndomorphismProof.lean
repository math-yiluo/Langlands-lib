import Langlands.GroupScheme.ImageGenerationNoetherianStatement
import Langlands.GroupScheme.ImageGenerationNoetherianProof

/-!
# Proof of `Langlands.GroupScheme.ImageGeneration.NoetherianAffineClosedEndomorphismStatement`

A named theorem for a statement that follows directly from published results.
-/

universe u

namespace Langlands.GroupScheme.ImageGeneration

/-- Proof of `NoetherianAffineClosedEndomorphismStatement`. -/
theorem noetherianAffineClosedEndomorphism : NoetherianAffineClosedEndomorphismStatement.{u} :=
  noetherianImageGenerationFiniteness.2

end Langlands.GroupScheme.ImageGeneration
