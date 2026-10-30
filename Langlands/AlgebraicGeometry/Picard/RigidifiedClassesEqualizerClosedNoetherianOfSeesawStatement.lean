import Langlands.AlgebraicGeometry.Picard.NoetherianLineBundleSeesawStatement
import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesEqualizerClosedNoetherianStatement
import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesZariskiSeparatedStatement
import Langlands.AbelianScheme.SmoothGeometricIntegralityStatement

/-! # The noetherian affine agreement locus from the noetherian seesaw -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- The closed agreement locus of two rigidified classes over a noetherian affine base follows
from the noetherian seesaw for line bundles on flat proper families, Zariski separatedness of
rigidified classes, and geometric integrality of smooth geometrically connected schemes over
fields. -/
def RigidifiedClassesEqualizerClosedNoetherianOfSeesawStatement : Prop :=
  NoetherianLineBundleSeesawStatement.{u} →
    RigidifiedClassesZariskiSeparatedStatement.{u} →
      SmoothGeometricIntegrality.{u} →
        RigidifiedClassesEqualizerClosedNoetherianAffineStatement.{u}

end Langlands.AbelianScheme
