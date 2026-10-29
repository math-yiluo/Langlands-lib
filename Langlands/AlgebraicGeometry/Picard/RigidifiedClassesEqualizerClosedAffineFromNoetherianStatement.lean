import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesEqualizerClosedAffineStatement
import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesEqualizerClosedNoetherianStatement
import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesNoetherianApproximationStatement

/-! # The affine agreement locus from the noetherian case and noetherian approximation -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- The closed agreement locus of two rigidified classes over an arbitrary affine base follows
from its noetherian case together with noetherian approximation of the agreement predicate. -/
def RigidifiedClassesEqualizerClosedAffineFromNoetherianStatement : Prop :=
  RigidifiedClassesEqualizerClosedNoetherianAffineStatement.{u} →
    RigidifiedClassesNoetherianApproximationStatement.{u} →
      RigidifiedClassesEqualizerClosedAffineStatement.{u}

end Langlands.AbelianScheme
