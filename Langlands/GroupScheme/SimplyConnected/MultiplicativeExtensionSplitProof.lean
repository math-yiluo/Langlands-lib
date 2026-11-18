import Langlands.GroupScheme.SimplyConnected.MultiplicativeExtensionReduction
import Langlands.GroupScheme.Torus.MultiplicativeTypeConnectedActionProof

/-! # Multiplicative-type extensions of simply connected semisimple groups split -/

universe u

namespace Langlands.GroupScheme

/-- Every faithfully flat multiplicative-type extension of a simply connected
semisimple field group splits by a homomorphism of group schemes. -/
theorem simplyConnectedMultiplicativeExtensionSplit :
    SimplyConnectedMultiplicativeExtensionSplitStatement.{u} :=
  simplyConnectedMultiplicativeExtensionSplit_of_connectedAction
    multiplicativeTypeConnectedAction

end Langlands.GroupScheme
