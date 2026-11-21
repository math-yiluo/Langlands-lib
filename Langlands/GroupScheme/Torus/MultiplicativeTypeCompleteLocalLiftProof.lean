import Langlands.GroupScheme.Torus.MultiplicativeTypeAdicLiftProof
import Langlands.GroupScheme.Torus.MultiplicativeTypeCompleteLocalLiftReduction

/-! # Lifting homomorphisms from groups of multiplicative type over complete local rings -/

universe u

namespace Langlands.GroupScheme

/-- Conrad, *Reductive group schemes*, Corollary B.3.5. Homomorphisms from a group of
multiplicative type to a smooth affine group over a complete local noetherian ring lift
from the special fibre. Lifts are conjugate by a point reducing to the identity, and
lifts of closed immersions are closed immersions. -/
theorem multiplicativeTypeCompleteLocalLift : MultiplicativeTypeCompleteLocalLiftStatement.{u} :=
  multiplicativeTypeCompleteLocalLift_of_adicLift multiplicativeTypeAdicLift

end Langlands.GroupScheme
