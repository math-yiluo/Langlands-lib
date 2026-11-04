import Langlands.GroupScheme.Derived.SmoothnessReduction
import Langlands.GroupScheme.ImageGenerationReducedProof

/-! # Smoothness of the scheme-theoretic derived subgroup -/

universe u

namespace Langlands.GroupScheme

/-- Every scheme-theoretic derived subgroup of a smooth affine locally finite type
group over a field is smooth. -/
theorem derivedSubgroupSmoothness : DerivedSubgroupSmoothnessStatement.{u} :=
  derivedSubgroupSmoothness_of_reducedImageGeneration
    ImageGeneration.geometricallyReducedAffineImageGeneration

end Langlands.GroupScheme
