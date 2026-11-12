import Langlands.GroupScheme.ImageGenerationNoetherianStatement
import Langlands.GroupScheme.ImageGenerationNoetherianProof

/-!
# Proof of `Langlands.GroupScheme.ImageGeneration.NoetherianPrimeChainStabilizationStatement`

A named theorem for a statement that follows directly from published results.
-/

universe u

namespace Langlands.GroupScheme.ImageGeneration

/-- Proof of `NoetherianPrimeChainStabilizationStatement`. -/
theorem noetherianPrimeChainStabilization : NoetherianPrimeChainStabilizationStatement.{u} :=
  noetherianImageGenerationFiniteness.1

end Langlands.GroupScheme.ImageGeneration
