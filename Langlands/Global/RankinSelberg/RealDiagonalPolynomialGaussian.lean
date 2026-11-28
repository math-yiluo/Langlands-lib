import Langlands.Global.RankinSelberg.ArchimedeanDeterminantTheta
import Langlands.LocalFactor.Archimedean.RealTatePolynomialGaussian

/-! # Polynomial Gaussian zeta integrals on the real diagonal -/

noncomputable section

open Complex MeasureTheory MvPolynomial
open scoped Real

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.ArchimedeanDeterminantTheta

open Langlands.LocalFactor.RealTate (integrand zeta monomialGaussian monomialGaussian_apply
  integrable_integrand zeta_monomialGaussian)

variable {n : ℕ}

/-- A polynomial times the product of the standard real Gaussians on the diagonal. -/
def diagonalPolynomialGaussian (P : MvPolynomial (Fin n) ℂ) (x : Fin n → ℝ) : ℂ :=
  eval (fun i => (x i : ℂ)) P * ∏ i, exp (-(π : ℂ) * (x i : ℂ) ^ 2)

theorem diagonalPolynomialGaussian_eq_exp (P : MvPolynomial (Fin n) ℂ) (x : Fin n → ℝ) :
    diagonalPolynomialGaussian P x = eval (fun i => (x i : ℂ)) P *
      (Real.exp (-π * ∑ i, x i ^ 2) : ℂ) := by
  unfold diagonalPolynomialGaussian
  rw [← Complex.exp_sum, ofReal_exp]
  push_cast
  rw [Finset.mul_sum]

private def diagonalMonomial (m : Fin n →₀ ℕ) (x : Fin n → ℝ) : ℂ :=
  ∏ i, monomialGaussian (m i) (x i)

private theorem diagonalPolynomialGaussian_eq_sum (P : MvPolynomial (Fin n) ℂ) (x : Fin n → ℝ) :
    diagonalPolynomialGaussian P x = ∑ m ∈ P.support, P.coeff m * diagonalMonomial m x := by
  have hEval := congrArg (eval (fun i => (x i : ℂ))) P.as_sum
  simp only [map_sum] at hEval
  unfold diagonalPolynomialGaussian
  rw [hEval, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), mul_assoc,
    ← Finset.prod_mul_distrib]
  simp only [diagonalMonomial, monomialGaussian_apply]

private theorem integrand_eq_mul (f : ℝ → ℂ) (e : Fin 2) (u : ℂ) (x : ℝ) :
    integrand f e u x = f x * integrand (fun _ => 1) e u x := by
  by_cases hx : x = 0 <;> simp [integrand, hx, mul_assoc]

private theorem weightedKernel_diagonalMonomial (e : Fin n → Fin 2) (u : Fin n → ℂ)
    (m : Fin n →₀ ℕ) (x : Fin n → ℝ) :
    weightedKernel e u (diagonalMonomial m) x =
      ∏ i, integrand (monomialGaussian (m i)) (e i) (u i) (x i) := by
  rw [weightedKernel, diagonalMonomial, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => (integrand_eq_mul (monomialGaussian (m i)) (e i) (u i) (x i)).symm

private theorem integrable_weightedKernel_diagonalMonomial (e : Fin n → Fin 2) (u : Fin n → ℂ)
    (hu : ∀ i, 0 < (u i).re) (m : Fin n →₀ ℕ) :
    Integrable (weightedKernel e u (diagonalMonomial m)) := by
  rw [funext (weightedKernel_diagonalMonomial e u m)]
  exact Integrable.fintype_prod fun i => integrable_integrand (monomialGaussian (m i)) (e i) (hu i)

private theorem integral_weightedKernel_diagonalMonomial (e : Fin n → Fin 2) (u : Fin n → ℂ)
    (m : Fin n →₀ ℕ) :
    ∫ x, weightedKernel e u (diagonalMonomial m) x =
      ∏ i, zeta (monomialGaussian (m i)) (e i) (u i) := by
  simp only [weightedKernel_diagonalMonomial, integral_fintype_prod_volume_eq_prod, zeta]

private theorem weightedKernel_diagonalPolynomialGaussian (P : MvPolynomial (Fin n) ℂ)
    (e : Fin n → Fin 2) (u : Fin n → ℂ) (x : Fin n → ℝ) :
    weightedKernel e u (diagonalPolynomialGaussian P) x =
      ∑ m ∈ P.support, P.coeff m * weightedKernel e u (diagonalMonomial m) x := by
  simp only [weightedKernel, diagonalPolynomialGaussian_eq_sum, Finset.sum_mul, mul_assoc]

/-- On a common-slope spectral line, the diagonal polynomial Gaussian has an absolutely
convergent integral equal to a polynomial times the product of the real parity factors. -/
def RealDiagonalPolynomialGaussianStatement : Prop :=
  ∀ (n : ℕ) (P : MvPolynomial (Fin n) ℂ) (e : Fin n → Fin 2) (t : Fin n → ℂ),
    ∃ Q : Polynomial ℂ, ∀ s : ℂ, (∀ i, 0 < (s + t i).re) →
      let K := weightedKernel e (fun i => s + t i) (diagonalPolynomialGaussian P)
      Integrable K ∧ (∫ x, K x) = Q.eval s * ∏ i, Gammaℝ (s + t i + (e i).val)

theorem realDiagonalPolynomialGaussian : RealDiagonalPolynomialGaussianStatement := by
  classical
  intro n P e t
  choose Q hQ using fun i m => zeta_monomialGaussian m (e i)
  let p (m : Fin n →₀ ℕ) (i : Fin n) := (Q i (m i)).comp (Polynomial.X + Polynomial.C (t i))
  refine ⟨∑ m ∈ P.support, Polynomial.C (P.coeff m) * ∏ i, p m i, fun s hs => ?_⟩
  let u (i : Fin n) := s + t i
  change Integrable (weightedKernel e u (diagonalPolynomialGaussian P)) ∧
    (∫ x, weightedKernel e u (diagonalPolynomialGaussian P) x) = _
  have hI (m : Fin n →₀ ℕ) := integrable_weightedKernel_diagonalMonomial e u hs m
  rw [funext (weightedKernel_diagonalPolynomialGaussian P e u)]
  refine ⟨integrable_finsetSum _ fun m _ => (hI m).const_mul _, ?_⟩
  rw [integral_finsetSum _ (fun m _ => (hI m).const_mul _)]
  simp only [integral_const_mul, integral_weightedKernel_diagonalMonomial, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod,
    Finset.sum_mul, mul_assoc, p, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
    ← Finset.prod_mul_distrib]
  refine Finset.sum_congr rfl fun m _ => congrArg (P.coeff m * ·) ?_
  exact Finset.prod_congr rfl fun i _ => hQ i (m i) (s + t i) (hs i)

end Langlands.Global.RankinSelbergGlobal.ArchimedeanDeterminantTheta
