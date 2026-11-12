import Langlands.GroupScheme.ImageGenerationStatement
import Langlands.GroupScheme.ImageEnvelopeStabilityProof
import Langlands.GroupScheme.ImageGenerationPointed
import Langlands.GroupScheme.SmoothConnectedGeometryProof

/-!
# Proof of `Langlands.GroupScheme.ImageGenerationSourceStatement`

A named theorem for a statement that follows directly from published results.
-/

universe u

namespace Langlands.GroupScheme

/-- Proof of `ImageGenerationSourceStatement`. -/
theorem imageGenerationSource : ImageGenerationSourceStatement.{u} :=
  ⟨smoothConnectedAffineGeometry, ImageGeneration.pointedImageGeneration,
    pointedImageEnvelopeStability⟩

end Langlands.GroupScheme
