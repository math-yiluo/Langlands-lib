import Langlands.GroupScheme.Torus.SolvableFixedContainmentConnectedReduction
import Langlands.GroupScheme.Torus.SolvableFixedAlgClosedCore

/-! # Proof: connected invariant subgroups containing torus fixed points -/

universe u

namespace Langlands.GroupScheme.Torus

/-- **Connected invariant subgroups containing the fixed subgroup.** Over any field, a smooth
closed subgroup of a smooth connected affine group that is solvable for all tests is connected
if it represents a stable subgroup functor containing the fixed subgroup of a split-torus
action. The algebraically closed case is `connectedSpace_of_isAlgClosed`; the algebraic-closure
reduction is `solvableFixedContainmentConnected_of_algClosed`. -/
theorem solvableFixedContainmentConnected : SolvableFixedContainmentConnectedStatement.{u} :=
  solvableFixedContainmentConnected_of_algClosed fun _ _ _ => connectedSpace_of_isAlgClosed

end Langlands.GroupScheme.Torus
