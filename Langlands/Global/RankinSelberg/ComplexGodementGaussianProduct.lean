import Langlands.Global.RankinSelberg.ComplexGodementColumnProduct
import Langlands.Global.RankinSelberg.ComplexGodementGaussianPolynomial

/-! # Splitting complex Gaussian monomials at the last column -/

noncomputable section

open scoped Matrix.Norms.Operator SchwartzMap
open MvPolynomial

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodementGaussianProduct

open ComplexGodementColumnProduct ComplexGodementGaussianPolynomial

variable {m : ℕ}
private abbrev Mat (m n : ℕ) := Matrix (Fin m) (Fin n) ℂ

private def vectorEuclidean (m : ℕ) : (Fin m → ℂ) ≃L[ℝ] EuclideanSpace ℂ (Fin m) :=
  (WithLp.linearEquiv 2 ℝ (Fin m → ℂ)).symm.toContinuousLinearEquiv

private def columnCoordCLM (v : Fin m × Bool) : (Fin m → ℂ) →L[ℝ] ℂ :=
  (coordinatePartCLM v.2).comp (ContinuousLinearMap.proj v.1)

private def columnGaussianSchwartz (m : ℕ) : 𝓢(Fin m → ℂ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (vectorEuclidean m)
    (radialGaussian.postcompCLM Complex.ofRealCLM)

private theorem columnGaussianSchwartz_apply (v : Fin m → ℂ) :
    columnGaussianSchwartz m v = (Real.exp (-∑ i, ‖v i‖ ^ 2) : ℂ) := by
  change (Real.exp (-‖vectorEuclidean m v‖ ^ 2) : ℂ) = _
  rw [EuclideanSpace.norm_sq_eq]
  rfl

/-- A monomial in the real coordinates of a complex column times its radial Gaussian. -/
noncomputable def columnGaussianMonomial (d : Fin m × Bool → ℕ) : 𝓢(Fin m → ℂ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ
    (fun v => eval (fun i => columnCoordCLM i v) (monomial (Finsupp.equivFunOnFinite.symm d) 1))
    (columnGaussianSchwartz m)

private theorem eval_monomial_fintype {ι : Type*} [Fintype ι] (c : ι → ℂ) (d : ι →₀ ℕ) (a : ℂ) :
    eval c (monomial d a) = a * ∏ i, c i ^ d i := by
  rw [eval_monomial, Finsupp.prod_fintype]
  exact fun i => pow_zero (c i)

@[simp] theorem columnGaussianMonomial_apply (d : Fin m × Bool → ℕ) (v : Fin m → ℂ) :
    columnGaussianMonomial d v = (∏ i, coordinatePartCLM i.2 (v i.1) ^ d i) *
      (Real.exp (-∑ i, ‖v i‖ ^ 2) : ℂ) := by
  rw [columnGaussianMonomial, SchwartzMap.smulLeftCLM_apply_apply
    (eval_hasTemperateGrowth columnCoordCLM _), smul_eq_mul, columnGaussianSchwartz_apply,
    eval_monomial_fintype, one_mul]
  rfl

/-- The exponents of a rectangular monomial restricted to its leading square block. -/
def leadingExponents (d : Coordinates m (m + 1) →₀ ℕ) : Coordinates m m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => d (i.1, i.2.1.castSucc, i.2.2)

private theorem matrixGaussian_column_split (A : Mat m (m + 1)) :
    matrixGaussian A = matrixGaussian (leadingColumns A) * columnGaussianSchwartz m (lastColumn A) := by
  rw [columnGaussianSchwartz_apply]
  have hnorm : matrixSqNorm A = matrixSqNorm (leadingColumns A) + ∑ i, ‖lastColumn A i‖ ^ 2 := by
    unfold matrixSqNorm
    simp_rw [Fin.sum_univ_castSucc]
    rw [Finset.sum_add_distrib]
    rfl
  simp only [matrixGaussian, hnorm, neg_add, Real.exp_add, Complex.ofReal_mul]

/-- A Gaussian monomial splits as a product test on the leading square and the last column. -/
theorem gaussianMonomial_eq_columnProduct (d : Coordinates m (m + 1) →₀ ℕ) (a : ℂ) :
    gaussianPolynomial (monomial d a) =
      columnProduct (gaussianPolynomial (monomial (leadingExponents d) a))
        (columnGaussianMonomial fun i => d (i.1, Fin.last m, i.2)) := by
  apply SchwartzMap.ext
  intro A
  simp only [columnProduct_apply, gaussianPolynomial_apply, columnGaussianMonomial_apply,
    eval_monomial_fintype]
  rw [matrixGaussian_column_split, columnGaussianSchwartz_apply]
  have hprod : (∏ i, coordinates A i ^ d i) =
      (∏ i, coordinates (leadingColumns A) i ^ leadingExponents d i) *
        (∏ i : Fin m × Bool, coordinatePartCLM i.2 (lastColumn A i.1) ^ d (i.1, Fin.last m, i.2)) := by
    simp only [Fintype.prod_prod_type]
    simp_rw [Fin.prod_univ_castSucc]
    rw [Finset.prod_mul_distrib]
    rfl
  rw [hprod]
  ring

/-- Gaussian monomials are product tests across the final-column split. -/
def ComplexGodementGaussianProductStatement : Prop :=
  ∀ (m : ℕ) (d : Coordinates m (m + 1) →₀ ℕ) (a : ℂ),
    gaussianPolynomial (monomial d a) =
      columnProduct (gaussianPolynomial (monomial (leadingExponents d) a))
        (columnGaussianMonomial fun i => d (i.1, Fin.last m, i.2))

theorem complexGodementGaussianProduct : ComplexGodementGaussianProductStatement :=
  fun _ => gaussianMonomial_eq_columnProduct

end Langlands.Global.RankinSelbergGlobal.ComplexGodementGaussianProduct
