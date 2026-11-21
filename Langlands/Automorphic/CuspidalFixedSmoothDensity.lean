import Langlands.Automorphic.CuspidalFixedSmoothDensityStatement
import Langlands.Automorphic.CuspidalJointAdmissibility

/-! # Proof of fixed-level derivative density for actual cuspidal realizations -/

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 25000

open scoped Classical Matrix.Norms.Operator

namespace Langlands.Automorphic.CuspidalFixedSmoothDensity

open Langlands.Global

universe u

attribute [local instance] fixedSmoothRationalGroup fixedSmoothContinuousGroup fixedSmoothFiniteGroup
  fixedSmoothFormsGroup fixedSmoothStableGroup fixedSmoothSpaceGroup

/-- Joint admissibility supplies the fixed-level recovery used for density
of the original cuspidal smooth image. -/
theorem fixedLevelDensity : FixedLevelDensityStatement.{u} := by
  intro F _ _ _ r T b U J hU
  exact dense_fixedSmoothImage_of_jointRecovery F (r + 1) b U hU J
    (OperatorRealization.UnitaryForm.jointVectorRecovery b T.isJointlyAdmissible)

end Langlands.Automorphic.CuspidalFixedSmoothDensity
