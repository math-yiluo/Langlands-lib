import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesEqualizerClosedNoetherianOfSeesawProof
import Langlands.AlgebraicGeometry.Picard.NoetherianLineBundleSeesawProof
import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesZariskiSeparatedProof
import Langlands.AbelianScheme.SmoothGeometricIntegralityProof

/-! # Proof of the agreement locus over a noetherian affine base -/

universe u

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- Over a noetherian affine base, the locus where two actual rigidified classes agree is closed:
the published reduction applied to the noetherian seesaw, Zariski separatedness of rigidified
classes and smooth geometric integrality. -/
theorem rigidifiedClassesEqualizerClosedNoetherianAffine :
    RigidifiedClassesEqualizerClosedNoetherianAffineStatement.{u} :=
  rigidifiedClassesEqualizerClosedNoetherianAffine_of_seesaw noetherianLineBundleSeesaw
    rigidifiedClassesZariskiSeparated smoothGeometricIntegrality

end Langlands.AbelianScheme
