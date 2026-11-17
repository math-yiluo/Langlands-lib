import Langlands.BruhatTits.IntegralModels.UnramifiedFacetParabolicImageReduction
import Langlands.BruhatTits.IntegralModels.UnramifiedUpstairsRadicalRootGenerationProof
import Langlands.BruhatTits.IntegralModels.UnramifiedFacetPositiveRadicalProof
import Langlands.BruhatTits.IntegralModels.UnramifiedModelKernelProof

/-! # Parabolic images and reduction preimages for descended facet models -/

universe u

namespace Langlands.BruhatTits.IntegralModels

/-- **KP Axiom 4.1.22(2), (4)** for the characterized descended facet models,
with every hypothesis and quantifier of the published statement retained. -/
theorem unramifiedFacetParabolicImage : UnramifiedFacetParabolicImageStatement.{u} :=
  unramifiedFacetParabolicImage_of_generation_positive_modelKernel
    unramifiedUpstairsRadicalRootGeneration unramifiedFacetPositiveRadical
    unramifiedModelKernel

end Langlands.BruhatTits.IntegralModels
