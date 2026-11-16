import Langlands.BruhatTits.IntegralModels.UnramifiedFacetParabolicOrderReduction
import Langlands.BruhatTits.IntegralModels.UnramifiedUpstairsRadicalRootGenerationProof

/-! # The parabolic order bijection for descended unramified facet models -/

universe u

namespace Langlands.BruhatTits.IntegralModels

/-- The actual quotient images of incident facet models give the parabolic
bijection, and facet incidence reverses subgroup inclusion. -/
theorem unramifiedFacetParabolicOrder :
    UnramifiedFacetParabolicOrderStatement.{u} :=
  unramifiedFacetParabolicOrder_of_upstairs_rootGeneration
    unramifiedUpstairsRadicalRootGeneration

end Langlands.BruhatTits.IntegralModels
