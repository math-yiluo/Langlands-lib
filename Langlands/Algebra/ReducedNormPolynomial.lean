import Langlands.Algebra.SplitReducedNorm
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! Determinants of generic linear combinations, as actual homogeneous polynomials. -/

noncomputable section

namespace Langlands.ReducedNorm

universe uK uA uI uJ uR

open scoped TensorProduct
open MvPolynomial

variable {K : Type uK} [CommRing K]
  {I : Type uI} [Fintype I] [DecidableEq I]
  {J : Type uJ} [Fintype J]

/-- The matrix of linear forms attached to a finite family of matrices. -/
def genericMatrix (M : J → Matrix I I K) : Matrix I I (MvPolynomial J K) :=
  fun i j => ∑ k, C (M k i j) * X k

/-- The actual determinant polynomial of a finite linear family. -/
def detPolynomial (M : J → Matrix I I K) : MvPolynomial J K :=
  (genericMatrix M).det

/-- Coefficient extension commutes with the generic determinant polynomial. -/
theorem detPolynomial_map {R : Type uR} [CommRing R] (f : K →+* R)
    (M : J → Matrix I I K) :
    MvPolynomial.map f (detPolynomial M) = detPolynomial (fun k => (M k).map f) := by
  rw [detPolynomial, RingHom.map_det]
  congr 1
  ext i j
  simp [genericMatrix]

/-- Evaluation of the determinant polynomial is the determinant of the linear combination. -/
theorem detPolynomial_eval {R : Type uR} [CommRing R] (f : K →+* R)
    (M : J → Matrix I I K) (r : J → R) :
    eval₂ f r (detPolynomial M) = (∑ k, r k • (M k).map f).det := by
  rw [show eval₂ f r (detPolynomial M) = eval₂Hom f r (detPolynomial M) from rfl,
    detPolynomial, RingHom.map_det]
  congr 1
  ext i j
  simp [genericMatrix, Matrix.sum_apply, Matrix.smul_apply, mul_comm]

/-- Every monomial of the determinant polynomial has degree equal to the matrix size. -/
theorem detPolynomial_isHomogeneous (M : J → Matrix I I K) :
    (detPolynomial M).IsHomogeneous (Fintype.card I) := by
  classical
  have hentry (i j : I) : (genericMatrix M i j).IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ (fun k _ => isHomogeneous_C_mul_X _ _)
  rw [detPolynomial, Matrix.det_apply']
  apply IsHomogeneous.sum
  intro σ _
  have hprod := IsHomogeneous.prod Finset.univ (fun i => genericMatrix M (σ i) i)
    (fun _ => 1) (fun i _ => hentry (σ i) i)
  simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
    map_intCast] using hprod.C_mul (((Equiv.Perm.sign σ : ℤ) : K))

section Split

variable {K : Type uK} [Field K] {A : Type uA} [Ring A] [Algebra K A]

/-- Coordinate determinant polynomial of a split chart and a finite family in the algebra. -/
def chartPolynomial (e : A ≃ₐ[K] Matrix I I K) (a : J → A) : MvPolynomial J K :=
  detPolynomial (fun j => e (a j))

/-- The chart polynomial evaluates to the determinant norm on each tensor linear combination. -/
theorem chartPolynomial_eval [Nonempty I] (e : A ≃ₐ[K] Matrix I I K) (a : J → A)
    (R : Type uR) [CommRing R] [Algebra K R] (r : J → R) :
    eval₂ (algebraMap K R) r (chartPolynomial e a) =
      splitNorm e R (∑ j, r j ⊗ₜ[K] a j) := by
  rw [chartPolynomial, detPolynomial_eval, splitNorm_apply, map_sum]
  simp only [tensorChart_tmul]

/-- The polynomial itself, and therefore its coefficients, is independent of the chart. -/
theorem chartPolynomial_independent [Nonempty I] (e e' : A ≃ₐ[K] Matrix I I K)
    (a : J → A) : chartPolynomial e' a = chartPolynomial e a := by
  have h (f : A ≃ₐ[K] Matrix I I K) :
      chartPolynomial f a = splitNorm f (MvPolynomial J K) (∑ j, X j ⊗ₜ[K] a j) := by
    simpa using chartPolynomial_eval f a (MvPolynomial J K) X
  rw [h e', h e]
  exact splitNorm_chart_independent e e' _ _

end Split

end Langlands.ReducedNorm
