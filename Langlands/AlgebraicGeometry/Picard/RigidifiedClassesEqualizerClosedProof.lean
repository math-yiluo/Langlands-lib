import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesEqualizerClosedReductionProof
import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesEqualizerClosedAffineFromNoetherianProof
import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesEqualizerClosedNoetherianProof
import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesNoetherianApproximationProof
import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesZariskiSeparatedProof

/-! # The locus where two rigidified classes agree is closed (proof) -/

universe u

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- The agreement locus of two actual rigidified classes on an abelian scheme is represented by
a closed subscheme of the parameter scheme. -/
theorem rigidifiedClassesEqualizerClosed :
    RigidifiedClassesEqualizerClosedStatement.{u} :=
  rigidifiedClassesEqualizerClosedReduction
    (rigidifiedClassesEqualizerClosedAffine_of_noetherian
      rigidifiedClassesEqualizerClosedNoetherianAffine
      rigidifiedClassesNoetherianApproximation)
    rigidifiedClassesZariskiSeparated

end Langlands.AbelianScheme
