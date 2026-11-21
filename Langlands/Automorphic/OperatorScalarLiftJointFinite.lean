import Langlands.Automorphic.CuspidalAdmissible.CentralEigen
import Langlands.Automorphic.OperatorCompactCompatibility
import Langlands.Global.ArchimedeanCompactGroupFiniteProof
import Langlands.Global.ArchimedeanSeparateJointFiniteProof

/-! # Joint finiteness of covariant scalar lifts of original vectors -/

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 25000

namespace Langlands.Automorphic.OperatorRealization

open Langlands.Global Langlands.Global.ArchimedeanGL

universe u

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

attribute [local instance] cuspidalAdmCentralAddCommGroupRationalInvariant
  cuspidalAdmCentralAddCommGroupContinuousRational cuspidalAdmCentralAddCommGroupFiniteSmoothRational
  cuspidalAdmCentralAddCommGroupAutomorphicForms cuspidalAdmCentralAddCommGroupStableAutomorphic
  cuspidalAdmCentralAddCommGroupSpace

/-- Compact covariance and enveloping covariance pass the original
finiteness conditions to an actual scalar lift. -/
theorem scalarLift_isJointFinite (S : OperatorRealization F n)
    (C : S.Space →ₗ[ℂ] SmoothFunctions F n)
    (hK : ∀ k (v : S.Space), C (S.compactRepresentation k v) =
      ArchimedeanGL.smoothRightAction F n k.val (C v))
    (hD : ∀ a (v : S.Space), C (S.envelopingAction a v) = ArchimedeanGL.envelopingAction F n a (C v))
    (v : S.Space) : IsJointFinite F n (C v) := by
  have hmap : ArchimedeanGL.centerOrbitMap F n (C v) = C.comp (S.centerOrbitMap v) :=
    LinearMap.ext fun z => (hD z.val v).symm
  have hZ : ArchimedeanGL.IsCenterFinite F n (C v) := by
    change Module.Finite ℂ (ArchimedeanGL.centerOrbitSpan F n (C v))
    rw [ArchimedeanGL.centerOrbitSpan_eq_range, hmap, LinearMap.range_comp]
    have := S.finite_range_centerOrbitMap v
    infer_instance
  let κ := (ArchimedeanGL.smoothRightAction F n).comp (standardInfiniteCompact F n).subtype
  let j : S.compactRepresentation.IntertwiningMap κ :=
    { toLinearMap := C
      isIntertwining' k := LinearMap.ext (hK k) }
  have hk : FiniteVectors.IsFiniteVector κ (C v) :=
    (S.compactRepresentation_isFiniteVector v).map j
  exact separateJointFinite F n (C v) hZ (compactGroupFiniteDifferential F n (C v) hk)

end Langlands.Automorphic.OperatorRealization
