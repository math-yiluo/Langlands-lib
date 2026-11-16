import Langlands.CommutativeAlgebra.HenselianFiniteEtaleRefinementBridge
import Langlands.CommutativeAlgebra.HenselianFiniteEtaleRefinementViaWeil

/-! # Finite étale local refinement over a Henselian local ring -/

universe u

namespace Langlands.CommutativeAlgebra

/-- Every affine étale neighbourhood meeting the closed point of a Henselian
local ring admits a local finite étale refinement with the prescribed
factorization. -/
theorem henselianFiniteEtaleRefinement :
    HenselianFiniteEtaleRefinementStatement.{u} := by
  apply henselianFiniteEtaleRefinement_of_ring
  intro R _ _ A _ _ _ q _ _
  exact HenselianFiniteEtaleRefinement.exists_local_finite_etale_refinement_via_weil q

end Langlands.CommutativeAlgebra
