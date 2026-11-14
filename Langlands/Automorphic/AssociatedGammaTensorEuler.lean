import Langlands.Automorphic.Unramified.MatrixTraceGeneratingSeriesProof
import Langlands.LocalFactor.Euler.Definitions
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Euler polynomials of tensor products

If `det(1 - X A) = ∏_(a ∈ s) (1 - a X)` and `det(1 - X B) = ∏_(b ∈ t) (1 - b X)`, then
`det(1 - X (A ⊗ B)) = ∏_((a, b) ∈ s × t) (1 - a b X)`. The proof compares trace generating
series: the `k`-th coefficient is the trace of the `k`-th power, and traces are
multiplicative on tensor products.
-/

noncomputable section

set_option autoImplicit false

open Polynomial

namespace Langlands.Automorphic.Unramified

/-- The positive coefficients of the trace series of `∏_(r ∈ s) (1 - r X)` are power sums. -/
theorem coeff_polynomialTraceSeries_prod_linear (s : Multiset ℂ) {k : ℕ} (hk : 0 < k) :
    PowerSeries.coeff k (polynomialTraceSeries ((s.map fun r => 1 - C r * X).prod)) =
      (s.map fun r => r ^ k).sum := by
  have hfac : ∀ P ∈ s.map (fun r => 1 - C r * X), P.coeff 0 = 1 := by
    intro P hP
    obtain ⟨r, -, rfl⟩ := Multiset.mem_map.mp hP
    simp
  rw [polynomialTraceSeries_multiset_prod _ hfac, map_multiset_sum, Multiset.map_map,
    Multiset.map_map]
  congr 1
  exact Multiset.map_congr rfl fun r _ => coeff_polynomialTraceSeries_one_sub_C_mul_X r hk

/-- The constant coefficient of a trace series is zero. -/
theorem coeff_zero_polynomialTraceSeries (P : ℂ[X]) :
    PowerSeries.coeff 0 (polynomialTraceSeries P) = 0 := by
  rw [polynomialTraceSeries, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp

/-- The constant coefficient of `∏ (1 - r X)` is `1`. -/
theorem coeff_zero_prod_linear (s : Multiset ℂ) :
    ((s.map fun r => 1 - C r * X).prod).coeff 0 = 1 := by
  rw [Polynomial.coeff_zero_multiset_prod]
  refine Multiset.prod_eq_one fun c hc => ?_
  obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hc
  obtain ⟨r, -, rfl⟩ := Multiset.mem_map.mp hP
  simp

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

/-- The positive coefficients of the trace series of `det(1 - X M)` are the traces of the
powers of `M`. -/
theorem coeff_polynomialTraceSeries_eulerPolynomial (M : Module.End ℂ V) {k : ℕ}
    (hk : 0 < k) :
    PowerSeries.coeff k (polynomialTraceSeries (LocalFactor.eulerPolynomial M)) =
      LinearMap.trace ℂ V (M ^ k) := by
  classical
  let b := Module.finBasis ℂ V
  have h1 : LocalFactor.eulerPolynomial M = (LinearMap.toMatrix b b M).charpolyRev := by
    rw [LocalFactor.eulerPolynomial, ← LinearMap.charpoly_toMatrix M b, Matrix.reverse_charpoly]
  rw [h1, matrixTraceGeneratingSeries _ _ k hk, LinearMap.toMatrix_pow,
    ← LinearMap.trace_eq_matrix_trace ℂ b]

/-- Power sums over a product multiset factor. -/
theorem sum_map_product_pow (s t : Multiset ℂ) (k : ℕ) :
    ((s ×ˢ t).map fun z : ℂ × ℂ => (z.1 * z.2) ^ k).sum =
      (s.map fun r => r ^ k).sum * (t.map fun r => r ^ k).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.cons_product, Multiset.map_add, Multiset.sum_add, ih, Multiset.map_map,
      Multiset.map_cons, Multiset.sum_cons, add_mul]
    congr 1
    rw [← Multiset.sum_map_mul_left]
    exact congrArg Multiset.sum (Multiset.map_congr rfl fun r _ => by
      simp only [Function.comp_apply, mul_pow])

/-- **Tensor Euler polynomial.** -/
theorem eulerPolynomial_tensorMap (A : Module.End ℂ V) (B : Module.End ℂ W)
    (s t : Multiset ℂ)
    (hA : LocalFactor.eulerPolynomial A = (s.map fun r => 1 - C r * X).prod)
    (hB : LocalFactor.eulerPolynomial B = (t.map fun r => 1 - C r * X).prod) :
    LocalFactor.eulerPolynomial (TensorProduct.map A B) =
      ((s ×ˢ t).map fun z : ℂ × ℂ => 1 - C (z.1 * z.2) * X).prod := by
  have hRHS : ((s ×ˢ t).map fun z : ℂ × ℂ => 1 - C (z.1 * z.2) * X) =
      (((s ×ˢ t).map fun z : ℂ × ℂ => z.1 * z.2).map fun r => 1 - C r * X) := by
    rw [Multiset.map_map]
    rfl
  rw [hRHS]
  apply (polynomialTraceSeries_injective_normalized _ _
    (LocalFactor.eulerPolynomial_coeff_zero _) (coeff_zero_prod_linear _)).mp
  ext k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [coeff_zero_polynomialTraceSeries, coeff_zero_polynomialTraceSeries]
  · have htA := coeff_polynomialTraceSeries_eulerPolynomial A hk
    have htB := coeff_polynomialTraceSeries_eulerPolynomial B hk
    rw [hA, coeff_polynomialTraceSeries_prod_linear _ hk] at htA
    rw [hB, coeff_polynomialTraceSeries_prod_linear _ hk] at htB
    rw [coeff_polynomialTraceSeries_eulerPolynomial _ hk, TensorProduct.map_pow,
      LinearMap.trace_tensorProduct', ← htA, ← htB, coeff_polynomialTraceSeries_prod_linear _ hk,
      Multiset.map_map, ← sum_map_product_pow]
    rfl

end Langlands.Automorphic.Unramified
