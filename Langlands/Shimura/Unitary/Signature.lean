import Langlands.Shimura.Unitary.CMData
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-! # Hermitian adjoints and the actual archimedean signature condition -/

universe u v w

namespace Langlands.Shimura

namespace AlgebraInvolution

variable {R : Type*} {A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- The adjoint involution defined by an invertible self-adjoint element. -/
def adjoint (σ : AlgebraInvolution R A) (h : Aˣ) (hh : σ (h : A) = h) :
    AlgebraInvolution R A where
  linear :=
    { toFun a := (↑h⁻¹ : A) * σ a * h
      map_add' a b := by simp [mul_add, add_mul]
      map_smul' r a := by simp }
  map_one := by simp
  map_mul a b := by simp [mul_assoc]
  involutive a := by
    have hu : σ.units h = h := Units.ext hh
    have hi : σ (↑h⁻¹ : A) = (↑h⁻¹ : A) := by
      change (σ.units h⁻¹ : A) = _
      rw [σ.units_inv, hu]
    change (↑h⁻¹ : A) * σ ((↑h⁻¹ : A) * σ a * h) * h = a
    simp only [σ.apply_mul, σ.apply_apply, hh, hi]
    simp [mul_assoc]

@[simp] theorem adjoint_apply (σ : AlgebraInvolution R A) (h : Aˣ)
    (hh : σ (h : A) = h) (a : A) :
    σ.adjoint h hh a = (↑h⁻¹ : A) * σ a * h := rfl

end AlgebraInvolution

/-- The diagonal Hermitian matrix with `r` positive entries among `n` entries. -/
def signatureMatrix (n r : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun i => if i.val < r then 1 else -1

theorem signatureMatrix_sq (n r : ℕ) :
    signatureMatrix n r * signatureMatrix n r = 1 := by
  rw [signatureMatrix, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    split_ifs <;> norm_num
  · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]

theorem signatureMatrix_star (n r : ℕ) :
    star (signatureMatrix n r) = signatureMatrix n r := by
  ext i j
  simp only [Matrix.star_apply, signatureMatrix, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst j
    split_ifs <;> simp_all
  · simp [hij, Ne.symm hij]

/-- The actual invertible signature matrix; its inverse is itself. -/
def signatureUnit (n r : ℕ) : (Matrix (Fin n) (Fin n) ℂ)ˣ where
  val := signatureMatrix n r
  inv := signatureMatrix n r
  val_inv := signatureMatrix_sq n r
  inv_val := signatureMatrix_sq n r

/-- Adjoint with respect to the standard diagonal Hermitian form. -/
noncomputable def signatureAdjoint (n r : ℕ) :
    AlgebraInvolution ℝ (Matrix (Fin n) (Fin n) ℂ) :=
  (AlgebraInvolution.ofStar (R := ℝ) (A := Matrix (Fin n) (Fin n) ℂ)).adjoint
    (signatureUnit n r) (signatureMatrix_star n r)

/-- The actual standard unitary matrix group for this Hermitian form. -/
noncomputable def signatureUnitary (n r : ℕ) :
    Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ :=
  (signatureAdjoint n r).unitary

section Archimedean

open CategoryTheory NumberField Algebra
open scoped TensorProduct

variable {E : Type u} {K : Type v} {A : Type w}
variable [Field E] [NumberField E] [IsTotallyReal E]
variable [Field K] [NumberField K] [IsTotallyComplex K]
variable [Algebra E K] [IsQuadraticExtension E K]
variable [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower E K A]

/-- Signature is witnessed by an actual real algebra isomorphism compatible
with the scalar-extended involution, rather than by a free label. -/
def HasSignature (σ : SecondKindInvolution E K A) (τ : E →+* ℝ) (n r : ℕ) : Prop :=
  letI : Algebra E ℝ := τ.toAlgebra
  r ≤ n ∧ ∃ e : (ℝ ⊗[E] A) ≃ₐ[ℝ] Matrix (Fin n) (Fin n) ℂ,
    ∀ x, e (σ.involution.baseChange ℝ x) = signatureAdjoint n r (e x)

/-- Harris's single noncompact archimedean place, equation (1.1). -/
def HasHarrisSignature (σ : SecondKindInvolution E K A) (n : ℕ) : Prop :=
  1 < n ∧ ∃ distinguished : E →+* ℝ,
    HasSignature σ distinguished n (n - 1) ∧
      ∀ τ : E →+* ℝ, τ ≠ distinguished → HasSignature σ τ n n

/-- The inner form used in the totally definite case has compact signatures everywhere. -/
def HasDefiniteSignature (σ : SecondKindInvolution E K A) (n : ℕ) : Prop :=
  1 < n ∧ ∀ τ : E →+* ℝ, HasSignature σ τ n n

end Archimedean

end Langlands.Shimura
