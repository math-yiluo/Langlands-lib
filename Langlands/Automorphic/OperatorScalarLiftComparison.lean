import Langlands.Automorphic.CuspidalHilbertCoefficientComparison
import Langlands.Automorphic.OperatorScalarLiftJointFinite

/-! # Analytic comparison of scalar lifts at a fixed finite level -/

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

variable (S : OperatorRealization F n)

private theorem scalarLift_apply_compact
    (C : S.Space →ₗ[ℂ] SmoothFunctions F n)
    (hK : ∀ k (v : S.Space), C (S.compactRepresentation k v) =
      ArchimedeanGL.smoothRightAction F n k.val (C v))
    (k : standardInfiniteCompact F n) (v : S.Space) :
    (C v).val k.val = (C (S.compactRepresentation k v)).val 1 := by
  have h := congrArg (fun f : SmoothFunctions F n => f.val 1) (hK k v)
  exact (h.trans ((smoothRightAction_apply F n k.val 1 (C v)).trans
    (congrArg (C v).val (one_mul k.val)))).symm

/-- Agreement at the identity on an original fixed level determines both
covariant scalar lifts on the entire infinite adelic group at that level. -/
theorem scalarLifts_eq_of_agree_at_fixedLevel
    (J : Subgroup (FiniteAdelicGL F n))
    (C W : S.Space →ₗ[ℂ] SmoothFunctions F n)
    (hCK : ∀ k (v : S.Space), C (S.compactRepresentation k v) =
      ArchimedeanGL.smoothRightAction F n k.val (C v))
    (hWK : ∀ k (v : S.Space), W (S.compactRepresentation k v) =
      ArchimedeanGL.smoothRightAction F n k.val (W v))
    (hCD : ∀ a (v : S.Space), C (S.envelopingAction a v) = ArchimedeanGL.envelopingAction F n a (C v))
    (hWD : ∀ a (v : S.Space), W (S.envelopingAction a v) = ArchimedeanGL.envelopingAction F n a (W v))
    (h1 : ∀ v ∈ fixedVectors S.finiteRepresentation J, (C v).val 1 = (W v).val 1)
    (v : S.Space) (hv : v ∈ fixedVectors S.finiteRepresentation J) : C v = W v := by
  refine jointFinite_eq_of_compact_enveloping_values F n (C v) (W v)
    (S.scalarLift_isJointFinite C hCK hCD v) (S.scalarLift_isJointFinite W hWK hWD v) ?_
  intro a k
  let w := S.envelopingAction a v
  have hw : w ∈ fixedVectors S.finiteRepresentation J := fun d =>
    (S.finiteRepresentation_envelopingAction d a v).trans
      (congrArg (S.envelopingAction a) (hv d))
  have hkw : S.compactRepresentation k w ∈ fixedVectors S.finiteRepresentation J := fun d =>
    (S.finiteRepresentation_compactRepresentation d k w).trans
      (congrArg (S.compactRepresentation k) (hw d))
  have hEq : (C w).val k.val = (W w).val k.val :=
    (scalarLift_apply_compact S C hCK k w).trans
      ((h1 _ hkw).trans (scalarLift_apply_compact S W hWK k w).symm)
  exact (congrArg (fun f : SmoothFunctions F n => f.val k.val) (hCD a v).symm).trans
    (hEq.trans (congrArg (fun f : SmoothFunctions F n => f.val k.val) (hWD a v)))

end Langlands.Automorphic.OperatorRealization
