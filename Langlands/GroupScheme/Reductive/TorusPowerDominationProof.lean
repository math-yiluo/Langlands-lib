import Langlands.GroupScheme.Reductive.TorusDominationReduction
import Langlands.GroupScheme.Reductive.TorusGenerationProof
import Langlands.GroupScheme.ImageGenerationPointed

/-! # reductiveTorusPowerDomination: unconditional proof from published reductions -/

universe u

namespace Langlands.GroupScheme

/-- Over an infinite field, every connected reductive group receives a scheme morphism with dense image from some finite fiber power of a torus. -/
theorem reductiveTorusPowerDomination :
    ReductiveTorusPowerDominationStatement.{u} :=
  reductiveTorusPowerDomination_of_generation reductiveFiniteTorusGeneration
    ImageGeneration.pointedImageGeneration

end Langlands.GroupScheme
