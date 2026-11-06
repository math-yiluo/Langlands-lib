import Langlands.Algebra.ReducedNormPolynomial
import Mathlib.FieldTheory.Galois.Basic

/-! Galois invariance and coefficient descent of the determinant polynomial. -/

noncomputable section

namespace Langlands.ReducedNorm

universe uK uL uA uI uJ

open scoped TensorProduct
open MvPolynomial

variable {K : Type uK} [Field K] {L : Type uL} [Field L] [Algebra K L]
  {A : Type uA} [Ring A] [Algebra K A]
  {I : Type uI} [Fintype I] [DecidableEq I]
  {J : Type uJ} [Fintype J]

/-- Conjugate a splitting chart by a base-field automorphism of its coefficients. -/
def galoisTwistChart (e : L ⊗[K] A ≃ₐ[L] Matrix I I L) (σ : L ≃ₐ[K] L) :
    L ⊗[K] A ≃ₐ[L] Matrix I I L :=
  { toRingEquiv :=
      ((Algebra.TensorProduct.congr σ.symm (AlgEquiv.refl : A ≃ₐ[K] A)).toRingEquiv.trans
        e.toRingEquiv).trans σ.mapMatrix.toRingEquiv
    commutes' l := by
      change (e ((Algebra.TensorProduct.congr σ.symm (AlgEquiv.refl : A ≃ₐ[K] A))
        (algebraMap L (L ⊗[K] A) l))).map σ = algebraMap L (Matrix I I L) l
      simp only [Algebra.TensorProduct.algebraMap_apply,
        Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, map_one]
      change (e (algebraMap L (L ⊗[K] A) (σ.symm l))).map σ = _
      rw [e.commutes]
      ext i j
      by_cases h : i = j <;> simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal, h] }

@[simp] theorem galoisTwistChart_base (e : L ⊗[K] A ≃ₐ[L] Matrix I I L)
    (σ : L ≃ₐ[K] L) (a : A) :
    galoisTwistChart e σ (1 ⊗ₜ[K] a) = (e (1 ⊗ₜ[K] a)).map σ := by
  change (e ((Algebra.TensorProduct.congr σ.symm (AlgEquiv.refl : A ≃ₐ[K] A))
    (1 ⊗ₜ[K] a))).map σ = _
  simp

/-- The determinant polynomial of base-algebra elements is Galois fixed coefficientwise. -/
theorem splittingPolynomial_fixed [Nonempty I]
    (e : L ⊗[K] A ≃ₐ[L] Matrix I I L) (a : J → A) (σ : L ≃ₐ[K] L) :
    MvPolynomial.map σ.toRingHom (chartPolynomial e (fun j => 1 ⊗ₜ[K] a j)) =
      chartPolynomial e (fun j => 1 ⊗ₜ[K] a j) := by
  rw [chartPolynomial, detPolynomial_map]
  have h : (fun j => (e (1 ⊗ₜ[K] a j)).map σ.toRingHom) =
      (fun j => galoisTwistChart e σ (1 ⊗ₜ[K] a j)) := by
    funext j
    exact (galoisTwistChart_base e σ (a j)).symm
  rw [h]
  change chartPolynomial (galoisTwistChart e σ) (fun j => 1 ⊗ₜ[K] a j) = _
  exact chartPolynomial_independent e (galoisTwistChart e σ) _

section Galois

variable [FiniteDimensional K L] [IsGalois K L]

omit [Fintype J] in
/-- A coefficientwise fixed polynomial over a finite Galois extension comes from the base field. -/
theorem exists_polynomial_descent (P : MvPolynomial J L)
    (hP : ∀ σ : L ≃ₐ[K] L, MvPolynomial.map σ.toRingHom P = P) :
    ∃ Q : MvPolynomial J K, MvPolynomial.map (algebraMap K L) Q = P := by
  apply MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
  intro c hc
  obtain ⟨m, _, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hc
  apply (IsGalois.mem_range_algebraMap_iff_fixed (F := K) (E := L) _).mpr
  intro σ
  have h := congrArg (fun Q : MvPolynomial J L => Q.coeff m) (hP σ)
  rw [MvPolynomial.coeff_map] at h
  exact h

/-- The uniquely descended determinant polynomial for a supplied finite Galois splitting chart. -/
def descendedPolynomial [Nonempty I] (e : L ⊗[K] A ≃ₐ[L] Matrix I I L)
    (a : J → A) : MvPolynomial J K :=
  Classical.choose (exists_polynomial_descent
    (chartPolynomial e (fun j => 1 ⊗ₜ[K] a j)) (splittingPolynomial_fixed e a))

@[simp] theorem descendedPolynomial_map [Nonempty I]
    (e : L ⊗[K] A ≃ₐ[L] Matrix I I L) (a : J → A) :
    MvPolynomial.map (algebraMap K L) (descendedPolynomial e a) =
      chartPolynomial e (fun j => 1 ⊗ₜ[K] a j) :=
  Classical.choose_spec (exists_polynomial_descent
    (chartPolynomial e (fun j => 1 ⊗ₜ[K] a j)) (splittingPolynomial_fixed e a))

/-- The descended polynomial has genuine homogeneous degree equal to the splitting matrix size. -/
theorem descendedPolynomial_isHomogeneous [Nonempty I]
    (e : L ⊗[K] A ≃ₐ[L] Matrix I I L) (a : J → A) :
    (descendedPolynomial e a).IsHomogeneous (Fintype.card I) := by
  apply IsHomogeneous.of_map (FaithfulSMul.algebraMap_injective K L)
  rw [descendedPolynomial_map]
  exact detPolynomial_isHomogeneous _

/-- Uniqueness of descent makes the base polynomial independent of a chart over the same field. -/
theorem descendedPolynomial_chart_independent [Nonempty I]
    (e e' : L ⊗[K] A ≃ₐ[L] Matrix I I L) (a : J → A) :
    descendedPolynomial e' a = descendedPolynomial e a := by
  apply MvPolynomial.map_injective (algebraMap K L)
    (FaithfulSMul.algebraMap_injective K L)
  rw [descendedPolynomial_map, descendedPolynomial_map]
  exact chartPolynomial_independent e e' _

end Galois

end Langlands.ReducedNorm
