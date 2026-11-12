import Langlands.GroupScheme.ImageGenerationStatement
import Langlands.GroupScheme.ImageGenerationPointed
import Langlands.GroupScheme.ImageEnvelopeStabilityProof

/-! # Invariant pointed-image generation -/

universe u

namespace Langlands.GroupScheme

/-- The exact published proposition, with its structural inputs discharged. -/
theorem invariantPointedImageGeneration :
    InvariantPointedImageGenerationStatement.{u} :=
  invariantPointedImageGeneration_of_generation_and_stability
    ImageGeneration.pointedImageGeneration pointedImageEnvelopeStability

end Langlands.GroupScheme
