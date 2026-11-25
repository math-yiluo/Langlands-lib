import Langlands.Analysis.DixmierMalliavin.ExponentialKernel
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Order.CompletePartialOrder

/-!
# Iterated exponential kernels and the stage identity

For sequences of rates `a j > 0` and radii `r j > 0`, this file forms the iterated convolutions
`K_n = k_{a_0,r_0} ⋆ ⋯ ⋆ k_{a_n,r_n}` of the exponential kernels of `ExponentialKernel`
(nonnegative, of mass at most `1`, supported in `[0, ∑_{j ≤ n} 2 r_j]`), the differential operators
`T_n = ∏_{j < n} (1 - a_j⁻¹ d/dt)` with their coefficients `productCoeff`, and the remainder
kernels `ρ_n` (`stageRemainder`).

The main statement is `Line.stage_identity`: for smooth `F`,
`F(0) = ∫ (T_{n+1} F) K_n + ∑_{j ≤ n} ∫ F ρ_j`.
It is the step identity iterated: each new factor `k_{a_{n+1}, r_{n+1}}` costs one factor
`1 - a_{n+1}⁻¹ d/dt` on `F` and one remainder. Moving `T_{n+1}` to the other side is repeated
integration by parts, `∫ F^{(p)} ψ = (-1)^p ∫ F ψ^{(p)}`, which is where the coefficients of
`∏ (1 + a_j⁻¹ X)` (all nonnegative) appear in `ρ_{n+1}`.

All declarations are internal to the proof of
`Langlands.Analysis.DixmierMalliavin.exists_dirac_eq_tsum_iteratedDeriv_add` and live in the
namespace `Langlands.Analysis.DixmierMalliavin.Line`.
-/

namespace Langlands.Analysis.DixmierMalliavin

open MeasureTheory Set Filter Topology Real Function ContinuousLinearMap
open scoped ContDiff Convolution Pointwise

noncomputable section

namespace Line

/-- Iterated derivatives of a smooth function on `ℝ` are smooth. -/
theorem contDiff_iteratedDeriv_of_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : ContDiff ℝ ∞ f) (m : ℕ) : ContDiff ℝ ∞ (iteratedDeriv m f) := by
  rw [iteratedDeriv_eq_iterate]; exact hf.iterate_deriv m

/-- Iterated derivatives of a compactly supported function on `ℝ` are compactly supported. -/
theorem hasCompactSupport_iteratedDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : HasCompactSupport f) (m : ℕ) : HasCompactSupport (iteratedDeriv m f) := by
  induction m with
  | zero => simpa using hf
  | succ m ih => rw [iteratedDeriv_succ]; exact ih.deriv

/-- The derivative of the `m`-th derivative of a smooth function is its `(m + 1)`-st derivative. -/
theorem hasDerivAt_iteratedDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : ContDiff ℝ ∞ f) (m : ℕ) (x : ℝ) :
    HasDerivAt (iteratedDeriv m f) (iteratedDeriv (m + 1) f x) x := by
  rw [iteratedDeriv_succ]
  exact ((contDiff_iteratedDeriv_of_contDiff hf m).differentiable (by simp) x).hasDerivAt

/-- Iterated derivatives commute with the inclusion `ℝ → ℂ`. -/
theorem iteratedDeriv_ofReal {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (m : ℕ) :
    iteratedDeriv m (fun t => (f t : ℂ)) = fun t => ((iteratedDeriv m f t : ℝ) : ℂ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    exact ((hasDerivAt_iteratedDeriv hf m t).ofReal_comp).deriv

/-- The convolution of real functions, seen in `ℂ`, is the convolution of the complexified functions. -/
theorem ofReal_convolution (f g : ℝ → ℝ) (x : ℝ) :
    (((f ⋆[mul ℝ ℝ] g) x : ℝ) : ℂ) =
      ((fun t => (f t : ℂ)) ⋆[mul ℂ ℂ] (fun t => (g t : ℂ))) x := by
  rw [convolution_mul, convolution_mul, ← integral_complex_ofReal]
  push_cast; rfl

/-- Pairing a continuous function with a convolution `K ⋆ k` of compactly supported integrable
functions: `∫ G (K ⋆ k) = ∫ K(s) ∫ G(s + t) k(t) dt ds`, with the integrability of the right side. -/
theorem pairing_convolution {G K k : ℝ → ℂ} (hG : Continuous G) (hK : Integrable K)
    (hk : Integrable k) (hKc : HasCompactSupport K) (hkc : HasCompactSupport k) :
    Integrable (fun s => K s * ∫ t, G (s + t) * k t) ∧
      ∫ u, G u * (K ⋆[mul ℂ ℂ] k) u = ∫ s, K s * ∫ t, G (s + t) * k t := by
  obtain ⟨M, hM⟩ := (hKc.isCompact.add hkc.isCompact).exists_bound_of_continuousOn hG.continuousOn
  set Ψ : ℝ × ℝ → ℂ := fun p => G p.1 * (K p.2 * k (p.1 - p.2)) with hΨ
  have hconv : Integrable (fun p : ℝ × ℝ => mul ℂ ℂ (K p.2) (k (p.1 - p.2))) (volume.prod volume) :=
    hK.convolution_integrand (mul ℂ ℂ) hk
  have hΨi : Integrable Ψ (volume.prod volume) := by
    refine Integrable.mono' (hconv.norm.const_mul M) ?_ (Eventually.of_forall fun p => ?_)
    · exact (hG.comp continuous_fst).aestronglyMeasurable.mul hconv.aestronglyMeasurable
    · simp only [hΨ, mul_apply', norm_mul]
      by_cases h : K p.2 * k (p.1 - p.2) = 0
      · rw [mul_eq_zero] at h
        rcases h with h | h <;> simp [h]
      · rw [mul_eq_zero, not_or] at h
        have hp : p.1 ∈ tsupport K + tsupport k :=
          ⟨p.2, subset_tsupport _ h.1, p.1 - p.2, subset_tsupport _ h.2, by ring⟩
        have := hM p.1 hp
        calc ‖G p.1‖ * (‖K p.2‖ * ‖k (p.1 - p.2)‖) ≤ M * (‖K p.2‖ * ‖k (p.1 - p.2)‖) :=
              mul_le_mul_of_nonneg_right this (by positivity)
          _ = _ := rfl
  have hswap := integral_integral_swap (f := fun u s => Ψ (u, s)) hΨi
  have hinner : ∀ s, ∫ u, Ψ (u, s) = K s * ∫ t, G (s + t) * k t := by
    intro s
    rw [← integral_const_mul, ← integral_add_left_eq_self (fun u => Ψ (u, s)) s]
    congr 1; funext t; simp only [hΨ]; rw [add_sub_cancel_left]; ring
  refine ⟨?_, ?_⟩
  · have := hΨi.integral_prod_right
    simpa only [hinner] using this
  · calc ∫ u, G u * (K ⋆[mul ℂ ℂ] k) u = ∫ u, ∫ s, Ψ (u, s) := by
          congr 1; funext u
          rw [convolution_mul, ← integral_const_mul]
      _ = ∫ s, ∫ u, Ψ (u, s) := hswap
      _ = ∫ s, K s * ∫ t, G (s + t) * k t := by simp only [hinner]

/-- Integration by parts against a compactly supported `C¹` function. -/
theorem integral_deriv_mul {F ψ : ℝ → ℂ} (hF : ContDiff ℝ 1 F) (hψ : ContDiff ℝ 1 ψ)
    (hψc : HasCompactSupport ψ) : ∫ u, deriv F u * ψ u = -∫ u, F u * deriv ψ u := by
  have hFd : Differentiable ℝ F := hF.differentiable one_ne_zero
  have hψd : Differentiable ℝ ψ := hψ.differentiable one_ne_zero
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable (u := F) (v := ψ) (u' := deriv F)
    (v' := deriv ψ) (fun x _ => (hFd x).hasDerivAt) (fun x _ => (hψd x).hasDerivAt)
    ((hF.continuous.mul (hψ.continuous_deriv le_rfl)).integrable_of_hasCompactSupport
      hψc.deriv.mul_left)
    (((hF.continuous_deriv le_rfl).mul hψ.continuous).integrable_of_hasCompactSupport
      hψc.mul_left)
    ((hF.continuous.mul hψ.continuous).integrable_of_hasCompactSupport hψc.mul_left)
  rw [h, neg_neg]

/-- Repeated integration by parts: `∫ F^{(p)} ψ = (-1)^p ∫ F ψ^{(p)}` for smooth `F` and smooth
compactly supported `ψ`. -/
theorem integral_iteratedDeriv_mul {F ψ : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (p : ℕ) :
    ∫ u, iteratedDeriv p F u * ψ u = (-1) ^ p * ∫ u, F u * iteratedDeriv p ψ u := by
  induction p generalizing F with
  | zero => simp
  | succ p ih =>
    have hF' : ContDiff ℝ ∞ (deriv F) := (contDiff_infty_iff_deriv.1 hF).2
    rw [iteratedDeriv_succ', ih hF', pow_succ, mul_assoc]
    congr 1
    rw [integral_deriv_mul (hF.of_le (by simp))
      ((contDiff_iteratedDeriv_of_contDiff hψ p).of_le (by simp))
      (hasCompactSupport_iteratedDeriv hψc p), ← iteratedDeriv_succ]
    ring

/-- The coefficient of `X^p` in `∏_{j < n} (1 + a_j⁻¹ X)`, by the recursion in `n`. -/
def productCoeff (a : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, p => if p = 0 then 1 else 0
  | n + 1, 0 => productCoeff a n 0
  | n + 1, p + 1 => productCoeff a n (p + 1) + productCoeff a n p / a n

/-- The constant coefficient of `∏_{j < n} (1 + a_j⁻¹ X)` is `1`. -/
theorem productCoeff_zero_right (a : ℕ → ℝ) (n : ℕ) : productCoeff a n 0 = 1 := by
  induction n with
  | zero => simp [productCoeff]
  | succ n ih => simp [productCoeff, ih]

/-- `∏_{j < n} (1 + a_j⁻¹ X)` has degree at most `n`. -/
theorem productCoeff_eq_zero (a : ℕ → ℝ) {n p : ℕ} (h : n < p) : productCoeff a n p = 0 := by
  induction n generalizing p with
  | zero =>
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    simp [productCoeff]
  | succ n ih =>
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    simp [productCoeff, ih (by omega : n < q + 1), ih (by omega : n < q)]

/-- For positive rates the coefficients of `∏_{j < n} (1 + a_j⁻¹ X)` are nonnegative. -/
theorem productCoeff_nonneg {a : ℕ → ℝ} (ha : ∀ j, 0 < a j) (n p : ℕ) : 0 ≤ productCoeff a n p := by
  induction n generalizing p with
  | zero => simp only [productCoeff]; split_ifs <;> norm_num
  | succ n ih =>
    cases p with
    | zero => simp only [productCoeff]; exact ih 0
    | succ p => simp only [productCoeff]; exact add_nonneg (ih _) (div_nonneg (ih _) (ha n).le)

/-- The coefficient of `D^p` in `∏_{j < n} (1 - a_j⁻¹ D)`, as a complex number. -/
def signedCoeff (a : ℕ → ℝ) (n p : ℕ) : ℂ := (-1) ^ p * (productCoeff a n p : ℂ)

/-- The differential operator `T_n = ∏_{j < n} (1 - a_j⁻¹ d/dt)` applied to `F`, expanded as
`∑_{p ≤ n} signedCoeff a n p • F^{(p)}`. -/
def truncatedOperator (a : ℕ → ℝ) (n : ℕ) (F : ℝ → ℂ) (u : ℝ) : ℂ :=
  ∑ p ∈ Finset.range (n + 1), signedCoeff a n p * iteratedDeriv p F u

/-- The recursion of the signed coefficients: multiplying by `1 - a_n⁻¹ D`. -/
theorem sum_signedCoeff_succ (a : ℕ → ℝ) (n : ℕ) (d : ℕ → ℂ) :
    ∑ p ∈ Finset.range (n + 2), signedCoeff a (n + 1) p * d p =
      ∑ p ∈ Finset.range (n + 1), signedCoeff a n p * d p -
        (a n : ℂ)⁻¹ * ∑ p ∈ Finset.range (n + 1), signedCoeff a n p * d (p + 1) := by
  have key : ∀ p, signedCoeff a (n + 1) (p + 1) * d (p + 1) =
      signedCoeff a n (p + 1) * d (p + 1) - (a n : ℂ)⁻¹ * (signedCoeff a n p * d (p + 1)) := by
    intro p; simp only [signedCoeff, productCoeff]; push_cast; ring
  rw [Finset.sum_range_succ' _ (n + 1), Finset.sum_range_succ _ n,
    Finset.sum_range_succ' (fun p => signedCoeff a n p * d p) n,
    Finset.sum_range_succ (fun p => signedCoeff a n p * d (p + 1)) n,
    Finset.sum_congr rfl (fun p _ => key p), Finset.sum_sub_distrib, ← Finset.mul_sum, key n]
  have h1 : signedCoeff a n (n + 1) = 0 := by
    simp [signedCoeff, productCoeff_eq_zero a (Nat.lt_succ_self n)]
  have h2 : signedCoeff a (n + 1) 0 = signedCoeff a n 0 := by
    simp [signedCoeff, productCoeff_zero_right]
  rw [h1, h2]
  ring

/-- `T_n F` is continuous for smooth `F`. -/
theorem continuous_truncatedOperator (a : ℕ → ℝ) (n : ℕ) {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) :
    Continuous (truncatedOperator a n F) :=
  continuous_finsetSum _ fun p _ => continuous_const.mul
    (hF.continuous_iteratedDeriv p (by exact_mod_cast le_top))

/-- The derivative of `T_n F` is `T_n F'`. -/
theorem hasDerivAt_truncatedOperator (a : ℕ → ℝ) (n : ℕ) {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (x : ℝ) :
    HasDerivAt (truncatedOperator a n F)
      (∑ p ∈ Finset.range (n + 1), signedCoeff a n p * iteratedDeriv (p + 1) F x) x := by
  have := HasDerivAt.sum (u := Finset.range (n + 1))
            (A := fun p y => signedCoeff a n p * iteratedDeriv p F y)
    (fun p _ => (hasDerivAt_iteratedDeriv hF p x).const_mul (signedCoeff a n p))
  have e : truncatedOperator a n F = ∑ i ∈ Finset.range (n + 1), fun y =>
    signedCoeff a n i * iteratedDeriv i F y := by
    funext y; simp [truncatedOperator, Finset.sum_apply]
  rw [e]; exact this

/-- `T_{n+1} F = T_n F - a_n⁻¹ (T_n F)'`. -/
theorem truncatedOperator_succ (a : ℕ → ℝ) (n : ℕ) (F : ℝ → ℂ) (u : ℝ) :
    truncatedOperator a (n + 1) F u = truncatedOperator a n F u -
      (a n : ℂ)⁻¹ * ∑ p ∈ Finset.range (n + 1), signedCoeff a n p * iteratedDeriv (p + 1) F u :=
  sum_signedCoeff_succ a n fun p => iteratedDeriv p F u

/-- The adjoint of `T_n`: `∫ (T_n F) ψ = ∫ F ∑_p productCoeff a n p ψ^{(p)}` for smooth compactly
supported `ψ`. -/
theorem integral_truncatedOperator_mul (a : ℕ → ℝ) (n : ℕ) {F ψ : ℝ → ℂ} (hF : ContDiff ℝ ∞ F)
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) :
    ∫ u, truncatedOperator a n F u * ψ u =
      ∫ u, F u * ∑ p ∈ Finset.range (n + 1), (productCoeff a n p : ℂ) * iteratedDeriv p ψ u := by
  have hint : ∀ p, Integrable fun u => signedCoeff a n p * iteratedDeriv p F u * ψ u := fun p =>
    ((continuous_const.mul (hF.continuous_iteratedDeriv p (by exact_mod_cast le_top))).mul
      hψ.continuous).integrable_of_hasCompactSupport hψc.mul_left
  have hint' : ∀ p,
      Integrable fun u => F u * ((productCoeff a n p : ℂ) * iteratedDeriv p ψ u) := fun p =>
    (hF.continuous.mul (continuous_const.mul
      (hψ.continuous_iteratedDeriv p (by exact_mod_cast le_top)))).integrable_of_hasCompactSupport
      ((hasCompactSupport_iteratedDeriv hψc p).mul_left.mul_left)
  simp only [truncatedOperator, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum _ fun p _ => hint p, integral_finsetSum _ fun p _ => hint' p]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [mul_assoc]
  rw [integral_const_mul, integral_iteratedDeriv_mul hF hψ hψc p, signedCoeff]
  have : ∫ u, F u * ((productCoeff a n p : ℂ) * iteratedDeriv p ψ u) =
      (productCoeff a n p : ℂ) * ∫ u, F u * iteratedDeriv p ψ u := by
    rw [← integral_const_mul]; congr 1; funext u; ring
  rw [this]
  have h1 : ((-1 : ℂ) ^ p) * ((-1) ^ p) = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
  linear_combination ((productCoeff a n p : ℂ) * ∫ u, F u * iteratedDeriv p ψ u) * h1

/-- The iterated convolution `K_n = k_{a_0,r_0} ⋆ ⋯ ⋆ k_{a_n,r_n}` of `n + 1` exponential kernels. -/
def kernelProduct (a r : ℕ → ℝ) : ℕ → ℝ → ℝ
  | 0 => expKernel (a 0) (r 0)
  | n + 1 => kernelProduct a r n ⋆[mul ℝ ℝ] expKernel (a (n + 1)) (r (n + 1))

/-- The bound `∑_{j ≤ n} 2 r_j` for the support of `K_n`. -/
def supportBound (r : ℕ → ℝ) (n : ℕ) : ℝ := ∑ j ∈ Finset.range (n + 1), 2 * r j

/-- The iterated convolution `K_n`, with complex values. -/
def kernelProductComplex (a r : ℕ → ℝ) (n : ℕ) : ℝ → ℂ := fun t => (kernelProduct a r n t : ℂ)

/-- The exponential kernel `k_{a_j,r_j}`, with complex values. -/
def expKernelComplex (a r : ℕ → ℝ) (j : ℕ) : ℝ → ℂ := fun t => (expKernel (a j) (r j) t : ℂ)

/-- The remainder `η_{a_j,r_j}`, with complex values. -/
def expRemainderComplex (a r : ℕ → ℝ) (j : ℕ) : ℝ → ℂ := fun t => (expRemainder (a j) (r j) t : ℂ)

/-- The remainder kernel of stage `n`: `ρ_0 = η_0`, and
`ρ_{n+1} = ∑_{p ≤ n+1} productCoeff a (n+1) p • (K_n ⋆ η_{n+1})^{(p)}`, the adjoint of `T_{n+1}`
applied to `K_n ⋆ η_{n+1}`. -/
def stageRemainder (a r : ℕ → ℝ) : ℕ → ℝ → ℂ
  | 0 => expRemainderComplex a r 0
  | n + 1 => fun u => ∑ p ∈ Finset.range (n + 2),
      (productCoeff a (n + 1) p : ℂ) * iteratedDeriv p
          (kernelProductComplex a r n ⋆[mul ℂ ℂ] expRemainderComplex a r (n + 1)) u

/-- The complex remainder kernels are smooth. -/
theorem contDiff_expRemainderComplex (a r : ℕ → ℝ) (j : ℕ) : ContDiff ℝ ∞
    (expRemainderComplex a r j) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_expRemainder _ _)

section Kernels

variable {a r : ℕ → ℝ} (ha : ∀ j, 0 < a j) (hr : ∀ j, 0 < r j)
include ha hr

omit ha in
/-- The complex remainder kernels have compact support. -/
theorem hasCompactSupport_expRemainderComplex (j : ℕ) : HasCompactSupport
    (expRemainderComplex a r j) :=
  (hasCompactSupport_expRemainder (hr j)).comp_left Complex.ofReal_zero

omit hr in
/-- `K_n` is nonnegative. -/
theorem kernelProduct_nonneg (n : ℕ) (t : ℝ) : 0 ≤ kernelProduct a r n t := by
  induction n generalizing t with
  | zero => exact expKernel_nonneg (ha 0).le _ _
  | succ n ih =>
    simp only [kernelProduct]; rw [convolution_mul]
    exact integral_nonneg fun s => mul_nonneg (ih s) (expKernel_nonneg (ha _).le _ _)

/-- `K_n` is integrable. -/
theorem integrable_kernelProduct (n : ℕ) : Integrable (kernelProduct a r n) := by
  induction n with
  | zero => exact integrable_expKernel (ha 0).le (hr 0)
  | succ n ih => exact ih.integrable_convolution (mul ℝ ℝ) (integrable_expKernel (ha _).le (hr _))

omit ha in
/-- `K_n` is supported in `[0, ∑_{j ≤ n} 2 r_j]`. -/
theorem support_kernelProduct_subset (n : ℕ) : support (kernelProduct a r n) ⊆ Icc 0
    (supportBound r n) := by
  induction n with
  | zero =>
    show support (expKernel (a 0) (r 0)) ⊆ _
    simpa [supportBound] using support_expKernel_subset (hr 0)
  | succ n ih =>
    refine (support_convolution_subset (mul ℝ ℝ)).trans ?_
    refine (Set.add_subset_add ih (support_expKernel_subset (hr _))).trans ?_
    refine (Set.Icc_add_Icc_subset _ _ _ _).trans (Icc_subset_Icc (by simp) (le_of_eq ?_))
    simp [supportBound, Finset.sum_range_succ]

omit ha in
/-- `K_n` has compact support. -/
theorem hasCompactSupport_kernelProduct (n : ℕ) : HasCompactSupport (kernelProduct a r n) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (support_kernelProduct_subset hr n)

/-- `K_n` has mass at most `1`. -/
theorem integral_kernelProduct_le_one (n : ℕ) : ∫ t, kernelProduct a r n t ≤ 1 := by
  induction n with
  | zero => exact integral_expKernel_le_one (ha 0) (hr 0)
  | succ n ih =>
    simp only [kernelProduct]
    rw [integral_convolution (mul ℝ ℝ) (integrable_kernelProduct ha hr n)
      (integrable_expKernel (ha _).le (hr _)), mul_apply']
    have h1 : 0 ≤ ∫ t, kernelProduct a r n t := integral_nonneg (kernelProduct_nonneg ha n)
    have h2 := integral_expKernel_le_one (ha (n + 1)) (hr (n + 1))
    nlinarith

omit ha hr in
/-- The complex `K_{n+1}` is `K_n ⋆ k_{n+1}`. -/
theorem kernelProductComplex_succ (n : ℕ) : kernelProductComplex a r (n + 1) = kernelProductComplex
    a r n ⋆[mul ℂ ℂ] expKernelComplex a r (n + 1) :=
  funext fun x => ofReal_convolution _ _ x

/-- The complex `K_n` is integrable. -/
theorem integrable_kernelProductComplex (n : ℕ) : Integrable (kernelProductComplex a r n) :=
    (integrable_kernelProduct ha hr n).ofReal

omit ha in
/-- The complex `K_n` has compact support. -/
theorem hasCompactSupport_kernelProductComplex (n : ℕ) : HasCompactSupport
    (kernelProductComplex a r n) :=
  (hasCompactSupport_kernelProduct hr n).comp_left Complex.ofReal_zero

/-- `K_n ⋆ η_{n+1}` is smooth, since `η_{n+1}` is smooth with compact support. -/
theorem contDiff_conv_expRemainderComplex (n : ℕ) : ContDiff ℝ ∞
    (kernelProductComplex a r n ⋆[mul ℂ ℂ] expRemainderComplex a r (n + 1)) := by
  have e : (kernelProductComplex a r n ⋆[mul ℂ ℂ] expRemainderComplex a r (n + 1)) =
      (kernelProductComplex a r n ⋆[mul ℝ ℂ] expRemainderComplex a r (n + 1)) := by
    funext x; simp only [convolution_def, mul_apply']
  rw [e]
  exact (hasCompactSupport_expRemainderComplex hr _).contDiff_convolution_right (mul ℝ ℂ)
    (integrable_kernelProductComplex ha hr n).locallyIntegrable (contDiff_expRemainderComplex a r _)

omit ha in
/-- `K_n ⋆ η_{n+1}` has compact support. -/
theorem hasCompactSupport_conv_expRemainderComplex (n : ℕ) :
    HasCompactSupport (kernelProductComplex a r n ⋆[mul ℂ ℂ] expRemainderComplex a r (n + 1)) :=
  (hasCompactSupport_kernelProductComplex hr n).convolution (mul ℂ ℂ)
      (hasCompactSupport_expRemainderComplex hr _)

/-- **The stage identity.** For smooth `F` and every `n`,
`F(0) = ∫ (T_{n+1} F) K_n + ∑_{j ≤ n} ∫ F ρ_j`.
Induction on `n`: the step identity for `t ↦ (T_{n+1} F)(s + t)` with rate `a_{n+1}` and
`T_{n+2} F = T_{n+1} F - a_{n+1}⁻¹ (T_{n+1} F)'`, integrated against `K_n(s)`, turns
`∫ (T_{n+1} F) K_n` into `∫ (T_{n+2} F) K_{n+1} + ∫ (T_{n+1} F) (K_n ⋆ η_{n+1})`, and the last term
is `∫ F ρ_{n+1}` by the adjoint formula. -/
theorem stage_identity {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (n : ℕ) :
    F 0 = (∫ u, truncatedOperator a (n + 1) F u * kernelProductComplex a r n u) +
      ∑ j ∈ Finset.range (n + 1), ∫ u, F u * stageRemainder a r j u := by
  induction n with
  | zero =>
    have hd : ∀ t, HasDerivAt F (deriv F t) t := fun t =>
      (hF.differentiable (by simp) t).hasDerivAt
    have h := step_identity (ha 0) (hr 0) hd (hF.continuous_deriv (by simp))
    rw [h, Finset.sum_range_one]
    congr 1
    congr 1; funext u
    have hT : truncatedOperator a 1 F u = F u - (a 0 : ℂ)⁻¹ * deriv F u := by
      simp [truncatedOperator, signedCoeff, productCoeff, Finset.sum_range_succ, iteratedDeriv_one];
          ring
    rw [hT]; rfl
  | succ n ih =>
    rw [ih, Finset.sum_range_succ _ (n + 1)]
    suffices hs : ∫ u, truncatedOperator a (n + 1) F u * kernelProductComplex a r n u =
        (∫ u, truncatedOperator a (n + 1 + 1) F u * kernelProductComplex a r (n + 1) u) + ∫ u, F u *
            stageRemainder a r (n + 1) u by
      rw [hs]; ring
    set G := truncatedOperator a (n + 1) F with hG
    set G2 := truncatedOperator a (n + 2) F with hG2
    have hGc : Continuous G := continuous_truncatedOperator a _ hF
    have hG2c : Continuous G2 := continuous_truncatedOperator a _ hF

    have hpt : ∀ s, G s = (∫ t, G2 (s + t) * expKernelComplex a r (n + 1) t) +
        ∫ t, G (s + t) * expRemainderComplex a r (n + 1) t := by
      intro s
      have hd : ∀ t, HasDerivAt (fun t => G (s + t))
          (∑ p ∈ Finset.range (n + 2),
            signedCoeff a (n + 1) p * iteratedDeriv (p + 1) F (s + t)) t :=
        fun t => (hasDerivAt_truncatedOperator a (n + 1) hF (s + t)).comp_const_add s t
      have hdc : Continuous fun t =>
          ∑ p ∈ Finset.range (n + 2), signedCoeff a (n + 1) p * iteratedDeriv (p + 1) F (s + t) :=
        continuous_finsetSum _ fun p _ => continuous_const.mul
          ((hF.continuous_iteratedDeriv (p + 1) (by exact_mod_cast le_top)).comp
            (continuous_const.add continuous_id))
      have h := step_identity (ha (n + 1)) (hr (n + 1)) hd hdc
      simp only [add_zero] at h
      rw [h]
      congr 1
      congr 1; funext t
      congr 1
      exact (truncatedOperator_succ a (n + 1) F (s + t)).symm
    have hpk :=
        pairing_convolution (k := expKernelComplex a r (n + 1)) hG2c
            (integrable_kernelProductComplex ha hr n)
      (integrable_expKernel (ha (n + 1)).le (hr (n + 1))).ofReal
          (hasCompactSupport_kernelProductComplex hr n)
      ((HasCompactSupport.of_support_subset_isCompact isCompact_Icc
        (support_expKernel_subset (hr (n + 1)))).comp_left Complex.ofReal_zero)
    have hpη :=
        pairing_convolution (k := expRemainderComplex a r (n + 1)) hGc
            (integrable_kernelProductComplex ha hr n)
      (integrable_expRemainder (hr (n + 1))).ofReal (hasCompactSupport_kernelProductComplex hr n)
      (hasCompactSupport_expRemainderComplex hr (n + 1))
    calc ∫ u, G u * kernelProductComplex a r n u
        = ∫ s, kernelProductComplex a r n s * ((∫ t, G2 (s + t) * expKernelComplex a r (n + 1) t) +
            ∫ t, G (s + t) * expRemainderComplex a r (n + 1) t) := by
          congr 1; funext s; rw [hpt s, mul_comm]
      _ = (∫ s, kernelProductComplex a r n s * ∫ t, G2 (s + t) * expKernelComplex a r (n + 1) t) +
            ∫ s, kernelProductComplex a r n s *
              ∫ t, G (s + t) * expRemainderComplex a r (n + 1) t := by
          simp only [mul_add]; exact integral_add hpk.1 hpη.1
      _ = (∫ u, G2 u * kernelProductComplex a r (n + 1) u) +
            ∫ u, F u * stageRemainder a r (n + 1) u := by
          rw [← hpk.2, ← hpη.2, kernelProductComplex_succ n]
          congr 1
          rw [integral_truncatedOperator_mul a (n + 1) hF (contDiff_conv_expRemainderComplex ha hr n)
            (hasCompactSupport_conv_expRemainderComplex hr n)]
          rfl

end Kernels

end Line

end

end Langlands.Analysis.DixmierMalliavin
