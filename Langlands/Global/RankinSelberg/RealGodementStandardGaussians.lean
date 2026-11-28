import Langlands.Global.RankinSelberg.RealAdjacentGaussianSplit
import Langlands.Global.RankinSelberg.RealSquarePolynomialGaussian
import Langlands.Global.RankinSelberg.RealEqualPolynomialGeneration

/-! # Standard polynomial Gaussian tests for the real rectangular Godement integral -/

noncomputable section

open MvPolynomial
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodementGaussianPolynomial

open RealJacquet (columnGaussianMonomial columnGaussianMonomial_apply leadingExponents leadingColumns
  lastColumn gaussianMonomial_eq_realColumnProduct gaussianPolynomial_sum_monomials realColumnProduct
  realColumnProduct_apply)
open RealEqualPolynomialGeneration (IsGaussianPolynomialRow)
open RealSquarePolynomialGaussian (squarePolynomialGaussian)

local notation "Mat" => fun m n => Matrix (Fin m) (Fin n) ℝ

/-- The scalar `√π` taking the Gaussian of scale one to the standard real Gaussian. -/
def standardGaussianDilation : ℝˣ :=
  Units.mk0 (Real.sqrt Real.pi) (Real.sqrt_pos.2 Real.pi_pos).ne'

/-- Precomposition by the standard real Gaussian dilation. -/
def standardGaussianDilate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Φ : 𝓢(E, ℂ)) : 𝓢(E, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.smulLeft (R₁ := ℝ)
    (M₁ := E) standardGaussianDilation) Φ

@[simp] theorem standardGaussianDilate_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Φ : 𝓢(E, ℂ)) (x : E) :
    standardGaussianDilate Φ x = Φ (Real.sqrt Real.pi • x) := rfl

/-- A rectangular polynomial Gaussian test dilated to the standard real scale. -/
def standardMatrixTest {m n : ℕ} (p : MvPolynomial (Coordinates m n) ℂ) : 𝓢(Mat m n, ℂ) :=
  standardGaussianDilate (gaussianPolynomial p)

/-- A column monomial Gaussian test dilated to the standard real scale. -/
def standardColumnTest {r : ℕ} (d : Fin (r + 1) → ℕ) : 𝓢(Fin (r + 1) → ℝ, ℂ) :=
  standardGaussianDilate (columnGaussianMonomial d)

/-- Substitute `√π` times each variable in a polynomial multiplier. -/
def scalePolynomial {ι : Type*} (p : MvPolynomial ι ℂ) : MvPolynomial ι ℂ :=
  bind₁ (fun j => C (Real.sqrt Real.pi : ℂ) * X j) p

private theorem eval_scalePolynomial {ι : Type*} (p : MvPolynomial ι ℂ) (x : ι → ℝ) :
    eval (fun i => (x i : ℂ)) (scalePolynomial p) = eval (fun i => ((Real.sqrt Real.pi * x i : ℝ) : ℂ)) p := by
  change aeval (fun i => (x i : ℂ)) (scalePolynomial p) =
    aeval (fun i => ((Real.sqrt Real.pi * x i : ℝ) : ℂ)) p
  rw [scalePolynomial, aeval_bind₁]
  congr 2
  funext i
  rw [aeval_eq_eval, map_mul, eval_C, eval_X, Complex.ofReal_mul]

/-- The dilated rectangular test is a polynomial times the Gaussian of scale `π`. -/
theorem standardMatrixTest_apply {m n : ℕ} (p : MvPolynomial (Coordinates m n) ℂ) (A : Mat m n) :
    standardMatrixTest p A = eval (coordinates A) (scalePolynomial p) *
      (Real.exp (-Real.pi * matrixSqNorm A) : ℂ) := by
  have hN : matrixSqNorm (Real.sqrt Real.pi • A) = Real.pi * matrixSqNorm A := by
    simp only [matrixSqNorm, Matrix.smul_apply, smul_eq_mul, mul_pow, Real.sq_sqrt Real.pi_pos.le,
      Finset.mul_sum]
  rw [standardMatrixTest, standardGaussianDilate_apply, gaussianPolynomial_apply, matrixGaussian,
    hN, neg_mul]
  congr 1
  exact (eval_scalePolynomial p fun i => A i.1 i.2).symm

/-- The square block is a standard polynomial Gaussian with the scaled multiplier. -/
theorem standardMatrixTest_eq_squarePolynomialGaussian {m : ℕ}
    (p : MvPolynomial (Coordinates m m) ℂ) :
    (standardMatrixTest p : Mat m m → ℂ) = squarePolynomialGaussian (scalePolynomial p) := by
  funext A
  rw [standardMatrixTest_apply]
  rfl

/-- The column block lies in the standard polynomial Gaussian row class. -/
theorem standardColumnTest_isGaussianPolynomialRow {r : ℕ} (d : Fin (r + 1) → ℕ) :
    IsGaussianPolynomialRow Real.pi (standardColumnTest d) := by
  let e : Fin (r + 1) →₀ ℕ := Finsupp.equivFunOnFinite.symm d
  refine ⟨scalePolynomial (monomial e 1), fun x => ?_⟩
  change standardColumnTest d x = eval (fun i => (x i : ℂ)) (scalePolynomial (monomial e 1)) *
    (Real.exp (-Real.pi * ∑ i, x i ^ 2) : ℂ)
  rw [standardColumnTest, standardGaussianDilate_apply, columnGaussianMonomial_apply,
    eval_scalePolynomial, eval_monomial, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  have he (i : Fin (r + 1)) : e i = d i := rfl
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Real.sq_sqrt Real.pi_pos.le,
    ← Finset.mul_sum, neg_mul, he]

/-- Dilation to the standard scale commutes with the product of the square and column tests. -/
theorem standardMatrixTest_monomial {r : ℕ} (d : Coordinates (r + 1) (r + 2) →₀ ℕ) (a : ℂ) :
    standardMatrixTest (monomial d a) =
      realColumnProduct (standardMatrixTest (monomial (leadingExponents d) a))
        (standardColumnTest fun i => d (i, Fin.last (r + 1))) := by
  ext A
  simp only [standardMatrixTest, standardColumnTest, standardGaussianDilate_apply, realColumnProduct_apply]
  rw [gaussianMonomial_eq_realColumnProduct, realColumnProduct_apply]
  rfl

/-- A standard matrix test is the sum of its standard Gaussian monomials. -/
theorem standardMatrixTest_sum_monomials {m n : ℕ} (p : MvPolynomial (Coordinates m n) ℂ) :
    standardMatrixTest p = ∑ d ∈ p.support, standardMatrixTest (monomial d (p.coeff d)) := by
  ext A
  simp only [standardMatrixTest, standardGaussianDilate_apply, sum_apply]
  rw [gaussianPolynomial_sum_monomials p, sum_apply]

/-- At the standard real scale a rectangular polynomial Gaussian splits into a sum of
products of square polynomial Gaussians and column polynomial Gaussians. -/
def RealGodementStandardGaussianSplitStatement : Prop :=
  ∀ (r : ℕ) (p : MvPolynomial (Coordinates (r + 1) (r + 2)) ℂ),
    standardMatrixTest p = ∑ d ∈ p.support,
      realColumnProduct (standardMatrixTest (monomial (leadingExponents d) (p.coeff d)))
        (standardColumnTest fun i => d (i, Fin.last (r + 1)))

theorem realGodementStandardGaussianSplit : RealGodementStandardGaussianSplitStatement := by
  intro r p
  rw [standardMatrixTest_sum_monomials p]
  exact Finset.sum_congr rfl fun d _ => standardMatrixTest_monomial d (p.coeff d)

end Langlands.Global.RankinSelbergGlobal.RealGodementGaussianPolynomial
