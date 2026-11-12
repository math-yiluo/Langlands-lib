import Langlands.AlgebraicGeometry.Picard.MumfordBundlePicardZeroStatement
import Langlands.AlgebraicGeometry.Picard.MumfordBundlePicardZeroReduction
import Langlands.AbelianScheme.FieldCubePullbackProof
import Langlands.AlgebraicGeometry.Picard.FieldLineBundleTrivialityProof

/-! # The actual Mumford family is geometrically Picard zero -/

universe u

namespace Langlands.AbelianScheme

/-- Every geometric fibre of the actual Mumford family is translation invariant. -/
theorem mumfordBundlePicardZero : MumfordBundlePicardZeroStatement.{u} :=
  MumfordPicardZero.mumfordBundlePicardZero_of_cube
    Langlands.GroupScheme.fieldCubePullback
    Langlands.AlgebraicGeometry.Picard.fieldLineBundleTriviality

end Langlands.AbelianScheme
