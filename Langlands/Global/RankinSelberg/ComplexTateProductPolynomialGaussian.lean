import Langlands.Global.RankinSelberg.ComplexTatePolynomialGaussian
import Langlands.Global.RankinSelberg.ComplexTateProductContinuation

/-! # Polynomial normalizations of diagonal complex Tate products -/

noncomputable section

open Complex Filter MeasureTheory MvPolynomial Set
open scoped ComplexConjugate SchwartzMap Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexTateProduct

open Langlands.LocalFactor.ComplexTate (gaussian polynomialGaussian polynomialGaussian_apply
  complexTatePolynomialGaussian)

variable {n : ℕ}
local notation "Row" => Fin n → ℂ
local notation "Indices" => Fin n × Bool
local notation "Degrees" => Indices →₀ ℕ

/-- Complex coordinates and their conjugates in a fixed diagonal row. -/
def diagonalCoordinates (z : Row) (i : Indices) : ℂ := if i.2 then conj (z i.1) else z i.1

/-- The diagonal polynomial against the product of the scalar radial Gaussians of scale `2 * π`. -/
def diagonalPolynomialGaussian (P : MvPolynomial Indices ℂ) (z : Row) : ℂ :=
  eval (diagonalCoordinates z) P * ∏ j, gaussian 0 (z j)

private def scalarMonomial (ν : Degrees) (j : Fin n) : MvPolynomial Bool ℂ :=
  X false ^ ν (j, false) * X true ^ ν (j, true)

private theorem totalDegree_scalarMonomial_le (ν : Degrees) (j : Fin n) :
    (scalarMonomial ν j).totalDegree ≤ ν (j, false) + ν (j, true) := by
  simpa only [totalDegree_X_pow, scalarMonomial] using
    (totalDegree_mul (X false ^ ν (j, false) : MvPolynomial Bool ℂ) (X true ^ ν (j, true)))

private def diagonalMonomial (ν : Degrees) (x : Row) : ℂ :=
  ∏ j, polynomialGaussian (scalarMonomial ν j) (x j)

private theorem diagonalPolynomialGaussian_as_sum (P : MvPolynomial Indices ℂ) (z : Row) :
    diagonalPolynomialGaussian P z = ∑ ν ∈ P.support, P.coeff ν * diagonalMonomial ν z := by
  have hEval := congrArg (eval (diagonalCoordinates z)) P.as_sum
  simp only [map_sum] at hEval
  unfold diagonalPolynomialGaussian
  rw [hEval, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ν _
  rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type, mul_assoc]
  congr 1
  simp only [diagonalMonomial, polynomialGaussian_apply, scalarMonomial, map_pow, map_mul,
    eval_X, ite_true, Bool.false_eq_true, ite_false, Fintype.prod_bool, diagonalCoordinates]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rw [mul_comm ((conj (z j)) ^ ν (j, true))]

private theorem scalarIntegrand_eq (f : ℂ → ℂ) (m : ℤ) (u z : ℂ) :
    Langlands.LocalFactor.ComplexTate.integrand f m u z = f z * additiveWeight m u z := by
  by_cases hz : z = 0 <;> simp [Langlands.LocalFactor.ComplexTate.integrand,
    Langlands.LocalFactor.ComplexTate.direction, additiveWeight, hz, mul_assoc]

private theorem integrand_diagonalMonomial (ν : Degrees) (m : Fin n → ℤ) (u : Row) (z : Row) :
    integrand (diagonalMonomial ν) m u z =
      ∏ j, Langlands.LocalFactor.ComplexTate.integrand
        (polynomialGaussian (scalarMonomial ν j)) (m j) (u j) (z j) := by
  simp only [diagonalMonomial, integrand, scalarIntegrand_eq, Finset.prod_mul_distrib]

private theorem normalizedZeta_diagonalPolynomialGaussian (P : MvPolynomial Indices ℂ)
    (m : Fin n → ℤ) (u : Row) (hu : ∀ j, 0 < (u j).re) :
    normalizedZeta (diagonalPolynomialGaussian P) m u =
      ∑ ν ∈ P.support, P.coeff ν * ∏ j, ((1 / 2 : ℂ) *
        Langlands.LocalFactor.ComplexTate.normalizedZeta
          (polynomialGaussian (scalarMonomial ν j)) (m j) (u j)) := by
  classical
  have hsum (z : Row) : integrand (diagonalPolynomialGaussian P) m u z =
      ∑ ν ∈ P.support, P.coeff ν * integrand (diagonalMonomial ν) m u z := by
    simp only [integrand, diagonalPolynomialGaussian_as_sum, Finset.sum_mul, mul_assoc]
  have hI (ν : Degrees) : Integrable (integrand (diagonalMonomial ν) m u) volume := by
    rw [funext (integrand_diagonalMonomial ν m u)]
    exact Integrable.fintype_prod fun j => Langlands.LocalFactor.ComplexTate.integrable_integrand_volume
      (polynomialGaussian (scalarMonomial ν j)) (m j) (hu j)
  have hZ : zeta (diagonalPolynomialGaussian P) m u =
      ∑ ν ∈ P.support, P.coeff ν * zeta (diagonalMonomial ν) m u := by
    simp only [zeta, hsum, integral_finsetSum P.support (fun ν _ => (hI ν).const_mul _),
      integral_const_mul]
  rw [normalizedZeta, hZ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [mul_left_comm, zeta]
  simp only [integrand_diagonalMonomial, integral_fintype_prod_volume_eq_prod, ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  rw [Langlands.LocalFactor.ComplexTate.normalizedZeta_eq_right _ _ (hu j)]
  unfold Langlands.LocalFactor.ComplexTate.zeta Langlands.LocalFactor.ComplexTate.measure gammaNormalizer
  rw [integral_smul_measure]
  simp only [ENNReal.toReal_ofNat, Complex.real_smul, ofReal_ofNat]
  ring

/-- For a polynomial Gaussian on the diagonal, the entire product normalization on the
common-slope spectral line is a polynomial of degree bounded by the test polynomial. -/
def ComplexTateProductPolynomialGaussianStatement : Prop :=
  ∀ (n : ℕ) (H : 𝓢(Fin n → ℂ, ℂ) → (Fin n → ℤ) → (Fin n → ℂ) → ℂ), IsEntireNormalization H →
    ∀ (F : 𝓢(Fin n → ℂ, ℂ)) (P : MvPolynomial (Fin n × Bool) ℂ),
    (F : (Fin n → ℂ) → ℂ) = diagonalPolynomialGaussian P →
    ∀ (m : Fin n → ℤ) (t : Fin n → ℂ), ∃ Q : Polynomial ℂ,
      Q.natDegree ≤ P.totalDegree ∧ ∀ s, H F m (fun j => s + t j) = Q.eval s

set_option maxHeartbeats 600000 in
theorem complexTateProductPolynomialGaussian : ComplexTateProductPolynomialGaussianStatement := by
  classical
  intro n H hH F P hF m t
  choose B hBdeg hB using fun (ν : Fin n × Bool →₀ ℕ) j =>
    complexTatePolynomialGaussian (scalarMonomial ν j) (m j)
  let b (ν : Fin n × Bool →₀ ℕ) (j : Fin n) := Polynomial.C (1 / 2 : ℂ) *
    (B ν j).comp (Polynomial.X + Polynomial.C (t j))
  let Q := ∑ ν ∈ P.support, P.coeff ν • ∏ j, b ν j
  refine ⟨Q, ?_, fun s => congrFun (show (fun s => H F m (fun j => s + t j)) = Q.eval from ?_) s⟩
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro ν hν
    apply (Polynomial.natDegree_smul_le _ _).trans
    have hT := le_totalDegree hν
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_prod_type] at hT
    simp only [Fintype.sum_bool] at hT
    apply (Polynomial.natDegree_prod_le _ _).trans
    refine le_trans (Finset.sum_le_sum fun j _ => ?_) hT
    apply (Polynomial.natDegree_C_mul_le _ _).trans
    apply Polynomial.natDegree_comp_le.trans
    rw [Polynomial.natDegree_add_C, Polynomial.natDegree_X, mul_one, add_comm]
    exact (hBdeg ν j).trans (totalDegree_scalarMonomial_le ν j)
  · have hAnalytic : AnalyticOnNhd ℂ (fun s => H F m (fun j => s + t j)) univ := by
      intro s _
      have hParam (v : ℂ) : affineParameter t (fun _ => 1) v = fun j => v + t j := by
        funext j
        simp [affineParameter, add_comm]
      simpa only [hParam] using (hH.1 F m t (fun _ => 1)).analyticAt s
    let c := ∑ j, |(t j).re|
    let s₀ : ℂ := ((c + 1 : ℝ) : ℂ)
    have hs₀ : c < s₀.re := by simp [s₀]
    apply hAnalytic.eq_of_eventuallyEq (fun s _ => Q.differentiable.analyticAt s) (z₀ := s₀)
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs₀] with s hs
    have hpos (j : Fin n) : 0 < (s + t j).re := by
      rw [add_re]
      have hbound : |(t j).re| ≤ c := Finset.single_le_sum (fun i _ => abs_nonneg (t i).re) (Finset.mem_univ j)
      linarith [neg_abs_le (t j).re]
    rw [hH.2 _ _ _ hpos, hF, normalizedZeta_diagonalPolynomialGaussian _ _ _ hpos]
    simp only [Q, b, Polynomial.eval_finsetSum, Polynomial.smul_eq_C_mul, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_prod, Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_X, hB]

end Langlands.Global.RankinSelbergGlobal.ComplexTateProduct
