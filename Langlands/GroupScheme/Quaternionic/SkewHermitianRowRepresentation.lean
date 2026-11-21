import Langlands.GroupScheme.Quaternionic.ScalarQuadratic

/-! # Representation of skew values from a nonsingular isotropic row -/

noncomputable section

universe u v w

open Matrix

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
  {I : Type w} [Fintype I] [DecidableEq I] (τ : FirstKindInvolution R A)

omit [DecidableEq I] in
/-- Left coefficient multiplication in the first row argument. -/
theorem matrixSesqBilin_mul_left (H : Matrix I I A) (a : A) (x y : I → A) :
    τ.matrixSesqBilin H (fun i => a * x i) y = a * τ.matrixSesqBilin H x y := by
  simp [matrixSesqBilin_apply, Finset.mul_sum, mul_assoc]

omit [DecidableEq I] in
/-- Left coefficient multiplication in the second row argument acts by conjugation on the right. -/
theorem matrixSesqBilin_mul_right (H : Matrix I I A) (a : A) (x y : I → A) :
    τ.matrixSesqBilin H x (fun i => a * y i) = τ.matrixSesqBilin H x y * τ a := by
  simp [matrixSesqBilin_apply, Finset.sum_mul, τ.map_mul, mul_assoc]

/-- The negative adjoint condition makes the row pairing skew-hermitian. -/
theorem matrixSesqBilin_swap_of_skew {H : Matrix I I A} (hH : τ.matrix I H = -H) (x y : I → A) :
    τ.matrixSesqBilin H y x = -τ (τ.matrixSesqBilin H x y) := by
  have h (i j : I) : τ (H i j) = -H j i :=
    congrArg (fun M : Matrix I I A => M j i) hH
  simp only [matrixSesqBilin_apply, τ.map_sum, τ.map_mul, τ.apply_apply,
    h, mul_neg, neg_mul, ← Finset.sum_neg_distrib, neg_neg, mul_assoc]
  exact Finset.sum_comm

/-- A normalized partner for a row which has an invertible coordinate. -/
theorem matrixSesqBilin_exists_normalized_partner {H : Matrix I I A} (hH : IsUnit H)
    {x : I → A} {i : I} (hi : IsUnit (x i)) : ∃ y, τ.matrixSesqBilin H x y = 1 := by
  let z := (↑hH.unit⁻¹ : Matrix I I A) *ᵥ Pi.single i (↑hi.unit⁻¹ : A)
  let y := τ ∘ z
  have hz : H *ᵥ z = Pi.single i (↑hi.unit⁻¹ : A) := by
    rw [show z = (↑hH.unit⁻¹ : Matrix I I A) *ᵥ Pi.single i (↑hi.unit⁻¹ : A) from rfl,
      Matrix.mulVec_mulVec, hH.mul_val_inv, Matrix.one_mulVec]
  have hy : τ ∘ y = z := by
    funext j
    exact τ.apply_apply (z j)
  refine ⟨y, ?_⟩
  have hpair : τ.matrixSesqBilin H x y = x ⬝ᵥ (H *ᵥ (τ ∘ y)) := by
    simp only [matrixSesqBilin_apply, mulVec, dotProduct, Function.comp_apply, Finset.mul_sum, mul_assoc]
  rw [hpair, hy, hz, dotProduct_single, hi.mul_val_inv]

/-- An invertible skew Gram matrix with a nonsingular isotropic row represents
  every value on which its involution acts by negation. -/
def SkewHermitianRowRepresentationStatement : Prop :=
  ∀ (R : Type u) (A : Type v) [CommRing R] [Ring A] [Algebra R A] [Invertible (2 : R)]
    (I : Type w) [Fintype I] [DecidableEq I] (τ : FirstKindInvolution R A) (H : Matrix I I A),
    τ.matrix I H = -H → IsUnit H →
    ∀ (x : I → A) (i : I), IsUnit (x i) → τ.matrixSesqBilin H x x = 0 →
    ∀ c : A, τ c = -c → ∃ y, τ.matrixSesqBilin H y y = c

theorem skewHermitianRowRepresentation : SkewHermitianRowRepresentationStatement.{u, v, w} := by
  intro R A _ _ _ _ I _ _ τ H hH hu x i hi hxx c hc
  obtain ⟨y, hxy⟩ := τ.matrixSesqBilin_exists_normalized_partner hu hi
  let B := τ.matrixSesqBilin H
  have hyx : B y x = -1 := by rw [τ.matrixSesqBilin_swap_of_skew hH, hxy, τ.map_one]
  have hyy : τ (B y y) = -B y y := by
    have h := congrArg Neg.neg (τ.matrixSesqBilin_swap_of_skew hH y y)
    simpa only [neg_neg] using h.symm
  let a := (⅟ (2 : R)) • (c - B y y)
  have ha : τ a = -a := by
    change τ ((⅟ (2 : R)) • (c - B y y)) = -((⅟ (2 : R)) • (c - B y y))
    rw [τ.map_smul, τ.map_sub, hc, hyy, neg_sub_neg, ← neg_sub c (B y y), smul_neg]
  refine ⟨y + (fun j => a * x j), ?_⟩
  change B (y + (fun j => a * x j)) (y + (fun j => a * x j)) = _
  simp only [_root_.map_add, LinearMap.add_apply]
  change B y y + B (fun j => a * x j) y +
    (B y (fun j => a * x j) + B (fun j => a * x j) (fun j => a * x j)) = _
  simp only [B, τ.matrixSesqBilin_mul_left, τ.matrixSesqBilin_mul_right,
    hxy, hyx, hxx, ha, neg_one_mul, neg_neg, mul_one, zero_mul, mul_zero, add_zero]
  change B y y + a + a = _
  rw [add_assoc, show a + a = c - B y y from invOf_two_smul_add_invOf_two_smul R _,
    add_comm (B y y), sub_add_cancel]

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
