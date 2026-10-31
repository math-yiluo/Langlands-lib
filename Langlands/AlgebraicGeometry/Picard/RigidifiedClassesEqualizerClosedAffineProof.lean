import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesEqualizerClosedAffineFromNoetherianProof
import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesEqualizerClosedNoetherianProof
import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesNoetherianApproximationProof

/-! # Proof of the agreement locus over an affine base -/

universe u

namespace Langlands.AbelianScheme

/-- Over an affine base, the locus where two actual rigidified classes agree is closed: the
published reduction to the noetherian case, applied to the noetherian case and to noetherian
approximation of the agreement predicate. -/
theorem rigidifiedClassesEqualizerClosedAffine :
    RigidifiedClassesEqualizerClosedAffineStatement.{u} :=
  rigidifiedClassesEqualizerClosedAffine_of_noetherian
    rigidifiedClassesEqualizerClosedNoetherianAffine rigidifiedClassesNoetherianApproximation

end Langlands.AbelianScheme
