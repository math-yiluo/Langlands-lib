import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! # Smooth evaluation and derivatives of multivariate polynomials -/

noncomputable section

open scoped BigOperators ContDiff

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

namespace Langlands.AlgebraicGeometry.PointManifold

open MvPolynomial

variable {k ι : Type*} [NontriviallyNormedField k] [Fintype ι]

/-- The derivative of polynomial evaluation, expressed using formal partial derivatives. -/
def polynomialDerivative (p : MvPolynomial ι k) (x : ι → k) : (ι → k) →L[k] k :=
  ∑ i, eval x (pderiv i p) • ContinuousLinearMap.proj i

@[simp] theorem polynomialDerivative_apply (p : MvPolynomial ι k) (x v : ι → k) :
    polynomialDerivative p x v = ∑ i, eval x (pderiv i p) * v i := by
  simp [polynomialDerivative, smul_eq_mul]

@[simp] theorem polynomialDerivative_C (c : k) (x : ι → k) :
    polynomialDerivative (C c) x = 0 := by
  ext v
  simp

@[simp] theorem polynomialDerivative_add (p q : MvPolynomial ι k) (x : ι → k) :
    polynomialDerivative (p + q) x = polynomialDerivative p x + polynomialDerivative q x := by
  ext v
  simp [add_mul, Finset.sum_add_distrib]

@[simp] theorem polynomialDerivative_X (i : ι) (x : ι → k) :
    polynomialDerivative (X i) x = ContinuousLinearMap.proj i := by
  classical
  ext v
  simp [Pi.single_apply, apply_ite]

theorem polynomialDerivative_mul (p q : MvPolynomial ι k) (x : ι → k) :
    polynomialDerivative (p * q) x =
      eval x p • polynomialDerivative q x + eval x q • polynomialDerivative p x := by
  ext v
  simp only [polynomialDerivative_apply, add_apply, smul_apply, smul_eq_mul, pderiv_mul, map_add, map_mul]
  simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  ring

/-- Polynomial evaluation is smooth over the coefficient field. -/
theorem contDiff_polynomial_eval (p : MvPolynomial ι k) (n : WithTop ℕ∞) :
    ContDiff k n (fun x : ι → k => eval x p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa using (contDiff_const : ContDiff k n (fun _ : ι → k => c))
  | add p q hp hq => simpa using! hp.add hq
  | mul_X p i hp => simpa using hp.mul (contDiff_apply k k i)

/-- Analytic and formal derivatives of multivariate polynomial evaluation agree. -/
theorem hasFDerivAt_polynomial_eval (p : MvPolynomial ι k) (x : ι → k) :
    HasFDerivAt (fun y : ι → k => eval y p) (polynomialDerivative p x) x := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa using (hasFDerivAt_const c x)
  | add p q hp hq => simpa using! hp.add hq
  | mul_X p i hp =>
    simpa [polynomialDerivative_mul] using! hp.mul (hasFDerivAt_apply i x)

end Langlands.AlgebraicGeometry.PointManifold
