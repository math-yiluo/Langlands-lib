import Langlands.GroupScheme.CentralIsogeny.CommonRefinementOfPerfect
import Langlands.GroupScheme.Derived.SemisimplePerfectProof

/-! # Common semisimple refinement of two central isogenies -/

universe u

namespace Langlands.GroupScheme

/-- Two central isogenies `π : C ⟶ G` and `q : H ⟶ G` between semisimple field groups have a
common semisimple refinement: a semisimple `D` with central isogenies `p : D ⟶ C` and
`r : D ⟶ H` such that `p ≫ π = r ≫ q`. -/
theorem centralIsogenyCommonSemisimpleRefinement :
    CentralIsogenyCommonSemisimpleRefinement.{u} :=
  centralIsogenyCommonSemisimpleRefinement_of_perfect semisimplePerfect

end Langlands.GroupScheme
