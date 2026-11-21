import Langlands.Global.RankinSelberg.ComplexGodementGaussianProduct
import Langlands.Global.RankinSelberg.ComplexLocalPolynomialGaussian

/-! # Gaussian tests are finite sums of compact-finite column products -/

noncomputable section

open scoped Matrix.Norms.Operator SchwartzMap
open MvPolynomial

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodementGaussianProduct

open Langlands.Archimedean (unitaryCompact)
open ComplexGodementGaussianPolynomial (Coordinates coordinates coordinates_re coordinates_im
  gaussianPolynomial gaussianPolynomial_apply matrixGaussian matrixSqNorm)
open ComplexGodementColumnProduct (columnProduct)
open ComplexJacquet (ComplexMatrixPolynomialIndex complexMatrixPolynomialCoordinates
  complexMatrixPolynomialGaussian complexLocalPolynomialGaussian)

variable {m n : ℕ}

local notation "Mat" => Matrix (Fin m) (Fin n) ℂ

private def realCoordinatePolynomial (v : Coordinates m n) :
    MvPolynomial (ComplexMatrixPolynomialIndex m n) ℂ :=
  let X₁ := X (Sum.inl (v.1, v.2.1))
  let X₂ := X (Sum.inr (v.1, v.2.1))
  if v.2.2 then C (-(Complex.I / 2)) * (X₁ - X₂) else C (1 / 2) * (X₁ + X₂)

private theorem eval_realCoordinatePolynomial (A : Mat) (v : Coordinates m n) :
    aeval (complexMatrixPolynomialCoordinates A) (realCoordinatePolynomial v) = coordinates A v := by
  rcases v with ⟨i, j, b⟩
  cases b
  · change aeval _ (C (1 / 2) * (X _ + X _)) = ((A i j).re : ℂ)
    simp only [map_mul, map_add, aeval_C, aeval_X, complexMatrixPolynomialCoordinates,
      Algebra.algebraMap_self, RingHom.id_apply]
    rw [Complex.add_conj, Complex.ofReal_mul, Complex.ofReal_ofNat]
    ring
  · change aeval _ (C (-(Complex.I / 2)) * (X _ - X _)) = ((A i j).im : ℂ)
    simp only [map_mul, map_sub, aeval_C, aeval_X, complexMatrixPolynomialCoordinates,
      Algebra.algebraMap_self, RingHom.id_apply]
    rw [Complex.sub_conj, Complex.ofReal_mul, Complex.ofReal_ofNat]
    calc
      _ = -(Complex.I * Complex.I) * ((A i j).im : ℂ) := by ring
      _ = _ := by rw [Complex.I_mul_I, neg_neg, one_mul]

private theorem gaussianPolynomial_eq_complexCoordinates (p : MvPolynomial (Coordinates m n) ℂ)
    (A : Mat) :
    gaussianPolynomial p A = complexMatrixPolynomialGaussian 1 (bind₁ realCoordinatePolynomial p) A := by
  rw [gaussianPolynomial_apply, matrixGaussian, complexMatrixPolynomialGaussian, aeval_bind₁]
  simp_rw [eval_realCoordinatePolynomial]
  change _ = eval (coordinates A) p * Complex.exp (-(((1 : ℝ) * matrixSqNorm A : ℝ) : ℂ))
  rw [one_mul, ← Complex.ofReal_neg, ← Complex.ofReal_exp]

/-- Real-coordinate polynomial Gaussian tests have finite span under left unitary translation. -/
theorem finiteDimensional_gaussianPolynomial_left (p : MvPolynomial (Coordinates m n) ℂ) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : unitaryCompact ℂ m =>
      fun X : Mat => gaussianPolynomial p (k.val⁻¹.val * X))) := by
  have h :
      (fun (k : unitaryCompact ℂ m) (X : Mat) => gaussianPolynomial p (k.val⁻¹.val * X)) =
        fun k X => complexMatrixPolynomialGaussian 1 (bind₁ realCoordinatePolynomial p) (k.val⁻¹.val * X) :=
    funext fun k => funext fun X => gaussianPolynomial_eq_complexCoordinates p (k.val⁻¹.val * X)
  rw [h]
  exact (complexLocalPolynomialGaussian (m := m) (n := n) 1 (bind₁ realCoordinatePolynomial p)).2.1

/-- Use the Schwartz-valued linear map from polynomials to sum the monomials of a test. -/
def gaussianPolynomialLinear (m n : ℕ) :
    MvPolynomial (Coordinates m n) ℂ →ₗ[ℂ] 𝓢(Matrix (Fin m) (Fin n) ℂ, ℂ) where
  toFun := gaussianPolynomial
  map_add' p q := by
    ext X
    simp only [gaussianPolynomial_apply, map_add, add_apply, add_mul]
  map_smul' c p := by
    ext X
    simp only [gaussianPolynomial_apply, MvPolynomial.smul_eq_C_mul, map_mul, eval_C,
      smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]

theorem gaussianPolynomial_sum_monomials (p : MvPolynomial (Coordinates m n) ℂ) :
    gaussianPolynomial p = ∑ u ∈ p.support, gaussianPolynomial (monomial u (p.coeff u)) := by
  change gaussianPolynomialLinear m n p = ∑ u ∈ p.support, gaussianPolynomialLinear m n (monomial u (p.coeff u))
  rw [← map_sum, ← p.as_sum]

/-- Each rectangular polynomial Gaussian is a finite sum of monomial Gaussians
whose split square factors have finite left unitary orbit span. -/
def ComplexGodementSplitSpanningStatement : Prop :=
  ∀ (m : ℕ) (p : MvPolynomial (Coordinates m (m + 1)) ℂ),
    gaussianPolynomial p = ∑ u ∈ p.support, gaussianPolynomial (monomial u (p.coeff u)) ∧
    ∀ u ∈ p.support, ∃ (A : 𝓢(Matrix (Fin m) (Fin m) ℂ, ℂ)) (φ : 𝓢(Fin m → ℂ, ℂ)),
      gaussianPolynomial (monomial u (p.coeff u)) = columnProduct A φ ∧
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : unitaryCompact ℂ m =>
        fun X : Matrix (Fin m) (Fin m) ℂ => A (k.val⁻¹.val * X)))

theorem complexGodementSplitSpanning : ComplexGodementSplitSpanningStatement := by
  intro m p
  refine ⟨gaussianPolynomial_sum_monomials p, fun u _ => ?_⟩
  exact ⟨_, _, gaussianMonomial_eq_columnProduct u (p.coeff u), finiteDimensional_gaussianPolynomial_left _⟩

end Langlands.Global.RankinSelbergGlobal.ComplexGodementGaussianProduct
