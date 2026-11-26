import Langlands.Global.RankinSelberg.ComplexGodementDilation
import Langlands.Global.RankinSelberg.ComplexGodementGaussianColumnSplit
import Langlands.Global.RankinSelberg.ComplexEqualPolynomialGeneration
import Langlands.Global.RankinSelberg.ComplexSquareZetaPolynomialGaussian

/-! # Standard polynomial Gaussians for the split complex Godement integral -/

noncomputable section

open MvPolynomial
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodementGaussianPolynomial

open ComplexAdjacentUnfolding (dilateMatrixTest dilateMatrixTest_apply)
open ComplexGodementColumnProduct (columnProduct columnProduct_apply leadingColumns lastColumn)
open ComplexEqualPolynomialGeneration (IsGaussianPolynomialRow)
open ComplexSquareZeta (squarePolynomialGaussian)

local notation "Mat" => fun m n => Matrix (Fin m) (Fin n) ℂ
local notation "scale" => (2 * Real.pi : ℝ)

private def radius : ℝ := Real.sqrt scale

private theorem radius_pos : 0 < radius := Real.sqrt_pos.mpr (by positivity)

/-- A scalar dilation taking the Gaussian of scale one to the Gaussian of scale `2π`. -/
def standardGaussianDilation : ℂˣ :=
  Units.mk0 (radius : ℂ) (Complex.ofReal_ne_zero.mpr radius_pos.ne')

/-- A dilated polynomial Gaussian on a complex rectangular matrix space. -/
def standardMatrixTest {m n : ℕ} (p : MvPolynomial (Coordinates m n) ℂ) : 𝓢(Mat m n, ℂ) :=
  dilateMatrixTest standardGaussianDilation (gaussianPolynomial p)

/-- A dilated polynomial Gaussian on a single column. -/
def standardColumnTest {m : ℕ} (q : MvPolynomial (Coordinates m 1) ℂ) : 𝓢(Fin m → ℂ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((ContinuousLinearEquiv.smulLeft (R₁ := ℂ) (M₁ := Fin m → ℂ)
       standardGaussianDilation).restrictScalars ℝ) (columnGaussianPolynomial q)

/-- Substitute the standard scalar dilation in each real coordinate of the multiplier. -/
def scalePolynomial {ι : Type*} (p : MvPolynomial ι ℂ) : MvPolynomial ι ℂ :=
  bind₁ (fun j => C (radius : ℂ) * X j) p

private theorem matrixSqNorm_dilation {m n : ℕ} (A : Mat m n) :
    matrixSqNorm ((standardGaussianDilation : ℂ) • A) = scale * matrixSqNorm A := by
  change matrixSqNorm ((radius : ℂ) • A) = _
  simp only [matrixSqNorm, Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real,
    mul_pow, ← Finset.mul_sum, radius, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (by positivity : 0 ≤ scale)]

private theorem coordinates_dilation {m n : ℕ} (A : Mat m n) (i : Coordinates m n) :
    coordinates ((standardGaussianDilation : ℂ) • A) i = (radius : ℂ) * coordinates A i := by
  obtain ⟨i, j, b⟩ := i
  change coordinates ((radius : ℂ) • A) (i, j, b) = _
  cases b <;>
    simp only [coordinates_re, coordinates_im, Matrix.smul_apply, smul_eq_mul, Complex.re_ofReal_mul,
      Complex.im_ofReal_mul, Complex.ofReal_mul]

/-- The dilated rectangular test is an entry polynomial times the standard Gaussian. -/
theorem standardMatrixTest_apply {m n : ℕ} (p : MvPolynomial (Coordinates m n) ℂ) (A : Mat m n) :
    standardMatrixTest p A = eval (coordinates A) (scalePolynomial p) *
      (Real.exp (-scale * matrixSqNorm A) : ℂ) := by
  rw [standardMatrixTest, dilateMatrixTest_apply, gaussianPolynomial_apply, matrixGaussian,
    matrixSqNorm_dilation, neg_mul]
  congr 1
  change aeval (coordinates ((standardGaussianDilation : ℂ) • A)) p =
    aeval (coordinates A) (scalePolynomial p)
  rw [scalePolynomial, aeval_bind₁]
  congr 2
  funext i
  simp only [map_mul, aeval_C, aeval_X, Algebra.algebraMap_self, RingHom.id_apply, coordinates_dilation]

/-- The square block of a standard split test has the required square polynomial form. -/
theorem standardMatrixTest_eq_squarePolynomialGaussian {m : ℕ}
    (p : MvPolynomial (Coordinates m m) ℂ) :
    (standardMatrixTest p : Mat m m → ℂ) = squarePolynomialGaussian (scalePolynomial p) := by
  funext A
  rw [standardMatrixTest_apply]
  rfl

private theorem standardColumnTest_eq_matrix {m : ℕ} (q : MvPolynomial (Coordinates m 1) ℂ)
    (v : Fin m → ℂ) : standardColumnTest q v =
      standardMatrixTest q (Matrix.of fun i (_ : Fin 1) => v i) := rfl

/-- The column block of a standard split test belongs to the standard polynomial row class. -/
theorem standardColumnTest_isGaussianPolynomialRow {r : ℕ}
    (q : MvPolynomial (Coordinates (r + 1) 1) ℂ) :
    IsGaussianPolynomialRow scale (standardColumnTest q) := by
  refine ⟨rename (fun j => (j.1, j.2.2)) (scalePolynomial q), fun v => ?_⟩
  rw [standardColumnTest_eq_matrix, standardMatrixTest_apply, eval_rename]
  have hNorm : matrixSqNorm (Matrix.of fun i (_ : Fin 1) => v i) = ∑ i, ‖v i‖ ^ 2 := by
    simp only [matrixSqNorm, Matrix.of_apply, Fin.sum_univ_one]
  rw [hNorm]
  congr 2
  congr 1
  funext j
  obtain ⟨i, k, b⟩ := j
  cases b <;> rfl

/-- The fixed dilation of a rectangular polynomial Gaussian is a sum of split tests
with the standard Gaussian on both the square variables and the last column. -/
def ComplexGodementStandardGaussianSplitStatement : Prop :=
  ∀ (m : ℕ) (p : MvPolynomial (Coordinates m (m + 1)) ℂ),
    ∃ (l : ℕ) (A : Fin l → MvPolynomial (Coordinates m m) ℂ)
      (b : Fin l → MvPolynomial (Coordinates m 1) ℂ),
      standardMatrixTest p = ∑ j, columnProduct (standardMatrixTest (A j)) (standardColumnTest (b j))

theorem complexGodementStandardGaussianSplit : ComplexGodementStandardGaussianSplitStatement := by
  intro m p
  obtain ⟨l, A, b, h, _⟩ := complexGodementGaussianColumnSplit m p
  refine ⟨l, A, b, ?_⟩
  ext X
  simp only [standardMatrixTest, dilateMatrixTest_apply, h, sum_apply, columnProduct_apply]
  rfl

end Langlands.Global.RankinSelbergGlobal.ComplexGodementGaussianPolynomial
