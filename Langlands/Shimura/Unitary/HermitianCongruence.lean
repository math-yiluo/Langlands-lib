import Langlands.Shimura.Unitary.Signature
import Langlands.GroupScheme.SpecialLinearInnerForm.ConjugationDescent

/-! # Changing Gram matrices and twisting a unitary involution -/

noncomputable section

universe u v w

namespace Langlands.Shimura

open scoped TensorProduct

namespace AlgebraInvolution

variable {R B : Type*} [CommRing R] [Ring B] [Algebra R B]

/-- Changing the Hermitian Gram matrix by a symmetric unit composes its two adjoints. -/
theorem adjoint_adjoint_apply (θ : AlgebraInvolution R B) (H t : Bˣ)
    (hH : θ (H : B) = H) (ht : θ.adjoint H hH (t : B) = t)
    (hHt : θ (↑(H * t) : B) = ↑(H * t)) (x : B) :
    (θ.adjoint H hH).adjoint t ht x = θ.adjoint (H * t) hHt x := by
  simp only [adjoint_apply, _root_.mul_inv_rev, Units.val_mul, mul_assoc]

/-- The changed Gram matrix is Hermitian for the original anti-involution. -/
theorem adjoint_gram_mul (θ : AlgebraInvolution R B) (H t : Bˣ)
    (hH : θ (H : B) = H) (ht : θ.adjoint H hH (t : B) = t) :
    θ (↑(H * t) : B) = ↑(H * t) := by
  rw [Units.val_mul, θ.apply_mul, hH]
  have ht' := congrArg (fun x : B => (H : B) * x) ht
  simpa only [adjoint_apply, ← mul_assoc, Units.mul_inv, one_mul] using ht'

/-- Scalar extension transports a twist by a symmetric unit to the image of that unit. -/
theorem baseChange_adjoint_apply (θ : AlgebraInvolution R B) (t : Bˣ) (ht : θ (t : B) = t)
    (S : Type*) [CommRing S] [Algebra R S] (x : S ⊗[R] B) :
    (θ.adjoint t ht).baseChange S x =
      (1 ⊗ₜ[R] (↑t⁻¹ : B)) * θ.baseChange S x * (1 ⊗ₜ[R] (t : B)) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [apply_add, hx, hy, mul_add, add_mul]
  | tmul s x =>
    simp only [baseChange_tmul, adjoint_apply, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, mul_one]

end AlgebraInvolution

open NumberField _root_.Algebra

variable {E : Type u} {K : Type v} {A : Type w}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K] [Algebra E K] [IsQuadraticExtension E K]
  [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]

omit [NumberField E] in
/-- A twist of a second-kind involution by an invertible symmetric element. -/
def SecondKindInvolution.twist (σ : SecondKindInvolution E K A) (t : Aˣ)
    (ht : σ.involution (t : A) = t) : SecondKindInvolution E K A where
  involution := σ.involution.adjoint t ht
  onCenter z := by
    rw [AlgebraInvolution.adjoint_apply, σ.onCenter, mul_assoc,
      Algebra.commutes (cmConjugation E K z) (t : A), ← mul_assoc, Units.inv_mul, one_mul]

namespace FiniteUnitary

open Langlands.GroupScheme.SpecialLinearInnerForm

variable {R C : Type*} [CommRing R] [CommRing C] [Algebra R C] {n : ℕ}

local notation "M" => Matrix (Fin n) (Fin n) C

/-- The coordinate change by an invertible matrix acts by conjugation. -/
def matrixBasisChange (P : Mˣ) : M ≃ₐ[R] M where
  __ := conjugationAlgHom (R := R) P⁻¹
  invFun := conjugationAlgHom (R := R) P
  left_inv X := by simp [mul_assoc]
  right_inv X := by simp [mul_assoc]

@[simp] theorem matrixBasisChange_apply (P : Mˣ) (X : M) :
    matrixBasisChange (R := R) P X = (↑P⁻¹ : M) * X * (P : M) := rfl

/-- The coordinate change from `H` to its Gram congruence `G` intertwines the adjoints. -/
theorem matrixBasisChange_adjoint (θ : AlgebraInvolution R M) (H G P : Mˣ)
    (hH : θ (H : M) = H) (hG : θ (G : M) = G)
    (h : θ (P : M) * (H : M) * (P : M) = G) (X : M) :
    matrixBasisChange (R := R) P (θ.adjoint H hH X) =
      θ.adjoint G hG (matrixBasisChange (R := R) P X) := by
  have h' : θ.units P * H * P = G := Units.ext h
  have hi : θ ((↑P⁻¹ : M)) = (↑((θ.units P)⁻¹) : M) := rfl
  simp only [matrixBasisChange_apply, AlgebraInvolution.adjoint_apply,
    θ.apply_mul, hi, ← h', _root_.mul_inv_rev, Units.val_mul]
  simp only [← AlgebraInvolution.units_val θ P, mul_assoc, Units.inv_mul_cancel_left]

/-- Multiplying the Gram matrix by a central unit has no effect on the adjoint. -/
theorem adjoint_apply_of_scalar_gram (θ : AlgebraInvolution R M) (H G : Mˣ)
    (hH : θ (H : M) = H) (hG : θ (G : M) = G) (b : Cˣ)
    (h : H = Units.map (algebraMap C M).toMonoidHom b * G) (X : M) :
    θ.adjoint H hH X = θ.adjoint G hG X := by
  let B := Units.map (algebraMap C M).toMonoidHom b
  have hc : (B : M) * θ X = θ X * (B : M) := Algebra.commutes _ _
  have hcancel : (↑B⁻¹ : M) * θ X * (B : M) = θ X := by
    rw [mul_assoc, ← hc, ← mul_assoc, Units.inv_mul, one_mul]
  change H = B * G at h
  simp only [AlgebraInvolution.adjoint_apply, h, _root_.mul_inv_rev, Units.val_mul]
  calc
    _ = (↑G⁻¹ : M) * ((↑B⁻¹ : M) * θ X * (B : M)) * (G : M) := by
      simp only [mul_assoc]
    _ = _ := by rw [hcancel]

end FiniteUnitary

end Langlands.Shimura
