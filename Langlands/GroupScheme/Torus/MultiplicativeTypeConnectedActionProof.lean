import Langlands.GroupScheme.Torus.MultiplicativeTypeConnectedActionReduction
import Langlands.GroupScheme.Torus.DiagonalizableRigidityProof

/-! # Connected groups act trivially on groups of multiplicative type -/

universe u

namespace Langlands.GroupScheme

/-- Connected algebraic groups act trivially on groups of multiplicative type, and
normal closed subgroups of multiplicative type are central
(Milne, *Algebraic Groups* (2017), Corollaries 12.37 and 12.38). -/
theorem multiplicativeTypeConnectedAction : MultiplicativeTypeConnectedActionStatement.{u} :=
  multiplicativeTypeConnectedAction_of_diagonalizableRigidity diagonalizableRigidity

end Langlands.GroupScheme
