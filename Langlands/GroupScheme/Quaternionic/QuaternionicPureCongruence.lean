import Langlands.GroupScheme.Quaternionic.QuaternionConjugation
import Langlands.Algebra.ReducedNormScalarExtension

/-! # Congruence of pure quaternion values by an explicit rescaling -/

noncomputable section

universe u

open scoped TensorProduct

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

open Langlands.CentralSimple

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

section Norm

variable {F D R : Type u} [Field F] [CharZero F] [DivisionRing D] [Algebra F D]
  [Algebra.IsCentral F D] [FiniteDimensional F D] [Field R] [Algebra F R]

local notation "A" => R ⊗[F] D
local notation "N" => reducedNorm F D R

omit [CharZero F] in
/-- Scalar multiplication of a quaternion multiplies its reduced norm by a square. -/
theorem quaternion_reducedNorm_smul (hdim : Module.finrank F D = 4) (s : R) (x : A) :
    N (s • x) = s ^ 2 * N x := by
  rw [Algebra.smul_def, _root_.map_mul]
  change N (s ⊗ₜ[F] (1 : D)) * N x = _
  rw [reducedNorm_scalar, reducedDegree_eq_two_of_finrank_four hdim]

variable (σ : FirstKindInvolution F D) (hdim : Module.finrank F D = 4)
  (hsym : Module.finrank F σ.symmetricSubspace = 3)

local notation "barR" => FirstKindInvolution.baseChange (σ.quaternionConjugation hdim hsym) R

private theorem pure_mul_self {x : A} (hx : barR x = -x) :
    x * x = algebraMap R A (-(N x)) := by
  have h := σ.quaternionConjugation_norm_baseChange hdim hsym R x
  change x * barR x = _ at h
  rw [hx, mul_neg] at h
  simpa only [neg_neg, _root_.map_neg] using congrArg Neg.neg h

end Norm

/-- Rescale a pure quaternion congruence from the two indicated field squares.
  The conjugating element before scalar normalization is `1 + (s⁻¹ • y) * x⁻¹`. -/
def QuaternionicPureCongruenceStatement : Prop :=
  ∀ (F D R : Type u) [Field F] [CharZero F] [DivisionRing D] [Algebra F D]
    [Algebra.IsCentral F D] [FiniteDimensional F D] [Field R] [Algebra F R]
    (σ : FirstKindInvolution F D) (hdim : Module.finrank F D = 4)
    (hsym : Module.finrank F σ.symmetricSubspace = 3),
    let τ := (σ.quaternionConjugation hdim hsym).baseChange R
    let norm := reducedNorm F D R
    ∀ (x : (R ⊗[F] D)ˣ) (y : R ⊗[F] D), τ (x : R ⊗[F] D) = -↑x → τ y = -y →
    ∀ s : R, s ≠ 0 → norm y = s ^ 2 * norm x →
    let g := 1 + (s⁻¹ • y) * (↑x⁻¹ : R ⊗[F] D)
    norm g ≠ 0 → IsSquare (s / norm g) →
    ∃ u : (R ⊗[F] D)ˣ, (u : R ⊗[F] D) * ↑x * τ u = y

theorem quaternionicPureCongruence : QuaternionicPureCongruenceStatement.{u} := by
  intro F D R _ _ _ _ _ _ _ _ σ hdim hsym τ norm x y hx hy s hs hN g hg hsq
  let A := R ⊗[F] D
  let z := s⁻¹ • y
  have hz : τ z = -z := by
    change τ (s⁻¹ • y) = -(s⁻¹ • y)
    rw [τ.map_smul, hy, smul_neg]
  have hNz : norm z = norm x := by
    change reducedNorm F D R (s⁻¹ • y) = norm x
    rw [quaternion_reducedNorm_smul hdim, show reducedNorm F D R y = s ^ 2 * norm x from hN,
      ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hs, one_pow, one_mul]
  have hzz : z * z = (x : A) * ↑x := by
    rw [σ.pure_mul_self hdim hsym hz, σ.pure_mul_self hdim hsym hx,
      show reducedNorm F D R z = reducedNorm F D R (x : A) from hNz]
  have hgz : g * (x : A) = z * g := by
    change (1 + z * ↑x⁻¹) * (x : A) = z * (1 + z * ↑x⁻¹)
    rw [add_mul, one_mul, mul_assoc z, Units.inv_mul, mul_one, mul_add, mul_one, ← mul_assoc,
      hzz, mul_assoc, Units.mul_inv, mul_one, add_comm]
  obtain ⟨t, ht⟩ := hsq
  let w := t • g
  have hNw : norm w = s := by
    change reducedNorm F D R (t • g) = s
    rw [quaternion_reducedNorm_smul hdim, pow_two, ← ht, div_mul_cancel₀ _ hg]
  let C : CSA.{u, u} F := { toAlgCat := AlgCat.of F D }
  have hwu : IsUnit w := (isUnit_iff_reducedNorm_ne_zero C R w).mpr (hNw.trans_ne hs)
  refine ⟨hwu.unit, ?_⟩
  change (↑hwu.unit : A) * ↑x * τ ↑hwu.unit = y
  rw [hwu.unit_spec]
  have hwx : w * (x : A) = z * w := by
    change (t • g) * (x : A) = z * (t • g)
    rw [smul_mul_assoc, hgz, mul_smul_comm]
  have hww : w * τ w = algebraMap R (R ⊗[F] D) s := by
    exact (σ.quaternionConjugation_norm_baseChange hdim hsym R w).trans
      (congrArg (algebraMap R (R ⊗[F] D)) hNw)
  rw [hwx, mul_assoc, hww, ← Algebra.commutes (R := R) s z, ← Algebra.smul_def]
  change s • (s⁻¹ • y) = y
  rw [smul_smul, mul_inv_cancel₀ hs, one_smul]

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
