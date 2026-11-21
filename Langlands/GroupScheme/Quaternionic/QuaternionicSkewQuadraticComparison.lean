import Langlands.GroupScheme.Quaternionic.QuaternionicSkewIsometryTransport
import Langlands.GroupScheme.Quaternionic.QuaternionicProperWittDivision

/-! # The inverse to the skew Gram presentation of quaternionic quadratic forms -/

noncomputable section

universe u

open Matrix
open scoped TensorProduct

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1900000

section SkewForm

variable {F D : Type u} [Field F] [CharZero F] [DivisionRing D] [Algebra F D]
  [FiniteDimensional F D] (σ : FirstKindInvolution F D)
  (hdim : Module.finrank F D = 4) (hsym : Module.finrank F σ.symmetricSubspace = 3)
  {I : Type} [Fintype I] [DecidableEq I]

local notation "τ" => σ.quaternionConjugation hdim hsym
local notation "ℓ" => (σ.quaternionAlternatingUnit hdim hsym : D)

/-- The original quadratic model for a Gram matrix for canonical quaternion conjugation. -/
def quadraticOfConjugationSkewGram (H : Matrix I I D) : σ.QuadraticForms I :=
  Submodule.Quotient.mk (((2 : F)⁻¹) • (H * Matrix.scalar I ℓ))

omit [CharZero F] in
private theorem matrix_mul_alternatingUnit_adjoint (H : Matrix I I D) :
    σ.matrix I (H * Matrix.scalar I ℓ) = -((τ).matrix I H) * Matrix.scalar I ℓ := by
  ext i j
  simp only [FirstKindInvolution.matrix_apply, Matrix.scalar_apply, Matrix.neg_apply, Matrix.mul_diagonal]
  rw [σ.map_mul, σ.map_eq_neg_of_mem_alternating (σ.quaternionAlternatingUnit_mem hdim hsym), neg_mul]
  change -(ℓ * σ (H j i)) = -(ℓ * σ (H j i) * ℓ⁻¹) * ℓ
  rw [neg_mul, mul_assoc (ℓ * σ (H j i)), inv_mul_cancel₀ (σ.quaternionAlternatingUnit hdim hsym).ne_zero,
    mul_one]

/-- Multiplication by the alternating unit converts a skew Gram matrix to the polar Gram. -/
theorem polar_quadraticOfConjugationSkewGram {H : Matrix I I D} (hH : (τ).matrix I H = -H) :
    σ.polar (σ.quadraticOfConjugationSkewGram hdim hsym H) = H * Matrix.scalar I ℓ := by
  rw [quadraticOfConjugationSkewGram, polar_mk, FirstKindInvolution.map_smul,
    σ.matrix_mul_alternatingUnit_adjoint hdim hsym, hH, neg_neg,
    ← two_smul F, smul_smul, mul_inv_cancel₀ two_ne_zero, one_smul]

/-- The inverse presentation preserves nondegeneracy. -/
theorem isNondegenerate_quadraticOfConjugationSkewGram {H : Matrix I I D}
    (hH : (τ).matrix I H = -H) (hu : IsUnit H) :
    σ.IsNondegenerateQuadratic (σ.quadraticOfConjugationSkewGram hdim hsym H) := by
  change IsUnit (σ.polar _)
  rw [σ.polar_quadraticOfConjugationSkewGram hdim hsym hH]
  exact hu.mul ((σ.quaternionAlternatingUnit hdim hsym).isUnit.map (Matrix.scalar I))

/-- The skew Gram of the resulting quadratic form is the prescribed matrix. -/
theorem conjugationSkewGram_quadraticOfConjugationSkewGram {H : Matrix I I D}
    (hH : (τ).matrix I H = -H) :
    σ.conjugationSkewGram (σ.quadraticOfConjugationSkewGram hdim hsym H) hdim hsym = H := by
  change σ.polar (σ.quadraticOfConjugationSkewGram hdim hsym H) * Matrix.scalar I ℓ⁻¹ = H
  rw [σ.polar_quadraticOfConjugationSkewGram hdim hsym hH, Matrix.mul_assoc,
    ← _root_.map_mul (Matrix.scalar I), mul_inv_cancel₀ (σ.quaternionAlternatingUnit hdim hsym).ne_zero,
    _root_.map_one, Matrix.mul_one]

omit [CharZero F] in
/-- Values of the skew sesquilinear pairing are the original polar values times
  the inverse alternating unit on the right. -/
theorem sesqForm_conjugationSkewGram (q : σ.QuadraticForms I) (x y : I → D) :
    (τ).sesqForm (σ.conjugationSkewGram q hdim hsym) x y = σ.sesqForm (σ.polar q) x y * ℓ⁻¹ := by
  change (∑ i, ∑ j, x i * (σ.polar q * Matrix.scalar I ℓ⁻¹) i j * τ (y j)) = _
  simp only [Matrix.scalar_apply, Matrix.mul_diagonal, sesqForm, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change x i * (σ.polar q i j * ℓ⁻¹) * (ℓ * σ (y j) * ℓ⁻¹) =
    x i * σ.polar q i j * σ (y j) * ℓ⁻¹
  have h (a : D) : ℓ⁻¹ * (ℓ * a) = a := by
    rw [← mul_assoc, inv_mul_cancel₀ (σ.quaternionAlternatingUnit hdim hsym).ne_zero, one_mul]
  simp only [mul_assoc, h]

/-- Equal skew values in this model give equal quaternionic quadratic values. -/
theorem quadraticValue_eq_of_conjugationSkewGram_eq (q : σ.QuadraticForms I) {x y : I → D}
    (h : (τ).sesqForm (σ.conjugationSkewGram q hdim hsym) x x =
      (τ).sesqForm (σ.conjugationSkewGram q hdim hsym) y y) :
    σ.quadraticValue x q = σ.quadraticValue y q := by
  rw [σ.sesqForm_conjugationSkewGram hdim hsym, σ.sesqForm_conjugationSkewGram hdim hsym] at h
  have hp := mul_right_cancel₀ (inv_ne_zero (σ.quaternionAlternatingUnit hdim hsym).ne_zero) h
  have he := (Eichler.quotient_mk_sesqForm_polar_self σ q x).symm.trans
    ((congrArg (fun a : D => (Submodule.Quotient.mk a : D ⧸ σ.alternatingSubspace)) hp).trans
      (Eichler.quotient_mk_sesqForm_polar_self σ q y))
  rw [← two_smul F, ← two_smul F] at he
  exact smul_right_injective (D ⧸ σ.alternatingSubspace) (two_ne_zero : (2 : F) ≠ 0) he

omit [CharZero F] in
/-- A nonzero skew value has nonzero quaternionic quadratic value. -/
theorem quadraticValue_ne_zero_of_conjugationSkewGram_ne_zero (q : σ.QuadraticForms I) {x : I → D}
    (h : (τ).sesqForm (σ.conjugationSkewGram q hdim hsym) x x ≠ 0) :
    σ.quadraticValue x q ≠ 0 := by
  intro hq
  apply h
  rw [σ.sesqForm_conjugationSkewGram hdim hsym, σ.sesqForm_polar_self_eq_zero q x hq, zero_mul]

variable [Algebra.IsCentral F D]

/-- Proper transitivity for a canonical skew matrix over division coefficients,
  obtained from the original quaternionic quadratic model. -/
theorem exists_properIsometry_skewGram_division [Nonempty I] [LinearOrder I]
    {H : Matrix I I D} (hH : (τ).matrix I H = -H) {x y : I → D}
    (hx : (τ).sesqForm H x x ≠ 0) (hxy : (τ).sesqForm H x x = (τ).sesqForm H y y) :
    ∃ p : (Matrix I I D)ˣ, (p : Matrix I I D) * H * (τ).matrix I p = H ∧
      Langlands.CentralSimple.reducedNorm F (Matrix I I D) F ((1 : F) ⊗ₜ[F] (p : Matrix I I D)) = 1 ∧
      x ᵥ* (p : Matrix I I D) = y := by
  let q := σ.quadraticOfConjugationSkewGram hdim hsym H
  have hq : σ.conjugationSkewGram q hdim hsym = H :=
    σ.conjugationSkewGram_quadraticOfConjugationSkewGram hdim hsym hH
  obtain ⟨p, hp, hn, he⟩ := Eichler.exists_properIsometry_send σ q hdim
    (σ.quadraticValue_ne_zero_of_conjugationSkewGram_ne_zero hdim hsym q (hq.symm ▸ hx))
    (σ.quadraticValue_eq_of_conjugationSkewGram_eq hdim hsym q (hq.symm ▸ hxy))
  refine ⟨p, ?_, hn, he⟩
  apply Eichler.matrix_eq_of_sesqForm_eq τ
  intro a b
  rw [← (τ).sesqForm_vecMul, ← hq, σ.sesqForm_conjugationSkewGram hdim hsym,
    σ.sesqForm_conjugationSkewGram hdim hsym, Eichler.sesqForm_polar_vecMul_of_mem σ q hp]

end SkewForm

/-- Every invertible skew Gram for canonical quaternion conjugation comes
  from a nondegenerate form for the original orthogonal involution. -/
def QuaternionicSkewQuadraticComparisonStatement : Prop :=
  ∀ (F D : Type u) [Field F] [CharZero F] [DivisionRing D] [Algebra F D]
    [FiniteDimensional F D] [Algebra.IsCentral F D] (σ : FirstKindInvolution F D)
    (hdim : Module.finrank F D = 4) (hsym : Module.finrank F σ.symmetricSubspace = 3),
    ∀ (I : Type) [Fintype I] [DecidableEq I] (H : Matrix I I D),
      (σ.quaternionConjugation hdim hsym).matrix I H = -H → IsUnit H →
      ∃ q : σ.QuadraticForms I, σ.IsNondegenerateQuadratic q ∧ σ.conjugationSkewGram q hdim hsym = H

theorem quaternionicSkewQuadraticComparison : QuaternionicSkewQuadraticComparisonStatement.{u} := by
  intro F D _ _ _ _ _ _ σ hdim hsym I _ _ H hH hu
  exact ⟨σ.quadraticOfConjugationSkewGram hdim hsym H,
    σ.isNondegenerate_quadraticOfConjugationSkewGram hdim hsym hH hu,
    σ.conjugationSkewGram_quadraticOfConjugationSkewGram hdim hsym hH⟩

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
