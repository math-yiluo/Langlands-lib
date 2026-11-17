import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Langlands.Global.Hecke.MixedSpaceFourier

/-! # Polynomial Gaussians are Schwartz functions

For a real polynomial `P`, the function `x ↦ P(x) exp(-π x²)` is a Schwartz function on `ℝ`
(with complex values). Its derivative is `x ↦ (P'(x) - 2π x P(x)) exp(-π x²)`, so all iterated
derivatives are again polynomial Gaussians, and every polynomial Gaussian is bounded after
multiplication by `|x|^k`. In particular `x ↦ x^e exp(-π x²)` is Schwartz for `e ∈ {0, 1}`.
See the paired Markdown.
-/

noncomputable section

open Polynomial Real
open scoped SchwartzMap ContDiff

namespace Langlands.LocalFactor.RealTate

/-- The real-valued polynomial Gaussian `x ↦ P(x) exp(-π x²)`. -/
def gaussPoly (P : ℝ[X]) (x : ℝ) : ℝ :=
  P.eval x * Real.exp (-(π * x ^ 2))

/-- The polynomial `P' - 2π X P`, so that `(P e^{-πx²})' = (P' - 2π X P) e^{-πx²}`. -/
def gaussStep (P : ℝ[X]) : ℝ[X] :=
  derivative P - C (2 * π) * X * P

theorem hasDerivAt_gaussPoly (P : ℝ[X]) (x : ℝ) :
    HasDerivAt (gaussPoly P) (gaussPoly (gaussStep P) x) x := by
  have h1 : HasDerivAt (fun y : ℝ => -(π * y ^ 2)) (-(π * (2 * x))) x := by
    refine (((hasDerivAt_pow 2 x).const_mul π).neg).congr_deriv ?_
    norm_num
  have h2 : HasDerivAt (gaussPoly P) _ x := (P.hasDerivAt x).mul h1.exp
  refine h2.congr_deriv ?_
  simp only [gaussPoly, gaussStep, eval_sub, eval_mul, eval_C, eval_X]
  ring

theorem deriv_gaussPoly (P : ℝ[X]) : deriv (gaussPoly P) = gaussPoly (gaussStep P) :=
  funext fun x => (hasDerivAt_gaussPoly P x).deriv

theorem iteratedDeriv_gaussPoly (P : ℝ[X]) (n : ℕ) :
    iteratedDeriv n (gaussPoly P) = gaussPoly (gaussStep^[n] P) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, deriv_gaussPoly, Function.iterate_succ_apply']

theorem contDiff_gaussPoly (P : ℝ[X]) : ContDiff ℝ ∞ (gaussPoly P) :=
  contDiff_of_differentiable_iteratedDeriv (n := ⊤) fun m _ => by
    rw [iteratedDeriv_gaussPoly]
    exact fun x => (hasDerivAt_gaussPoly _ x).differentiableAt

/-- `|x|^m exp(-π x²)` is bounded. -/
theorem exists_abs_pow_mul_exp_le (m : ℕ) :
    ∃ C, ∀ x : ℝ, |x| ^ m * Real.exp (-(π * x ^ 2)) ≤ C := by
  obtain ⟨C, hC0, hC⟩ := Langlands.Global.Hecke.exists_pow_mul_exp_neg_le m Real.pi_pos
  refine ⟨C, fun x => ?_⟩
  have h := hC |x| (abs_nonneg x)
  rw [sq_abs] at h
  refine h.trans (mul_le_of_le_one_right hC0.le (Real.exp_le_one_iff.mpr ?_))
  have := sq_nonneg x
  have := Real.pi_pos
  nlinarith

/-- Every polynomial Gaussian is bounded after multiplication by `|x|^k`. -/
theorem exists_abs_pow_mul_gaussPoly_le (P : ℝ[X]) (k : ℕ) :
    ∃ C, ∀ x : ℝ, |x| ^ k * |gaussPoly P x| ≤ C := by
  choose B hB using fun i : ℕ => exists_abs_pow_mul_exp_le (k + i)
  refine ⟨∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i| * B i, fun x => ?_⟩
  have hP : |P.eval x| ≤ ∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i| * |x| ^ i := by
    rw [eval_eq_sum_range]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [abs_mul, abs_pow]
  rw [gaussPoly, abs_mul, Real.abs_exp]
  calc |x| ^ k * (|P.eval x| * Real.exp (-(π * x ^ 2)))
      ≤ |x| ^ k * ((∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i| * |x| ^ i) *
          Real.exp (-(π * x ^ 2))) := by gcongr
    _ = ∑ i ∈ Finset.range (P.natDegree + 1),
          |P.coeff i| * (|x| ^ (k + i) * Real.exp (-(π * x ^ 2))) := by
        rw [Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [pow_add]
        ring
    _ ≤ _ := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hB i x) (abs_nonneg _)

/-- The complex-valued Schwartz function `x ↦ P(x) exp(-π x²)`. -/
def gaussSchwartz (P : ℝ[X]) : 𝓢(ℝ, ℂ) where
  toFun x := (gaussPoly P x : ℂ)
  smooth' := Complex.ofRealCLM.contDiff.comp (contDiff_gaussPoly P)
  decay' k n := by
    obtain ⟨C, hC⟩ := exists_abs_pow_mul_gaussPoly_le (gaussStep^[n] P) k
    refine ⟨C, fun x => ?_⟩
    have h : ‖iteratedFDeriv ℝ n (fun x => (gaussPoly P x : ℂ)) x‖ =
        ‖iteratedFDeriv ℝ n (gaussPoly P) x‖ :=
      Complex.ofRealLI.norm_iteratedFDeriv_comp_left
        (contDiff_gaussPoly P).contDiffAt (by exact_mod_cast le_top)
    rw [h, norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_gaussPoly, Real.norm_eq_abs,
      Real.norm_eq_abs]
    exact hC x

theorem gaussSchwartz_apply (P : ℝ[X]) (x : ℝ) :
    gaussSchwartz P x = ((P.eval x : ℝ) : ℂ) * Complex.exp (-(π : ℂ) * (x : ℂ) ^ 2) := by
  change ((P.eval x * Real.exp (-(π * x ^ 2)) : ℝ) : ℂ) = _
  push_cast
  ring_nf

/-- The adapted Gaussian `x ↦ x^e exp(-π x²)` of parity `e` is a Schwartz function. -/
theorem exists_schwartz_gaussian (e : Fin 2) :
    ∃ f : 𝓢(ℝ, ℂ), ∀ x : ℝ,
      f x = (x : ℂ) ^ e.val * Complex.exp (-(π : ℂ) * (x : ℂ) ^ 2) := by
  refine ⟨gaussSchwartz (X ^ e.val), fun x => ?_⟩
  rw [gaussSchwartz_apply, eval_pow, eval_X]
  push_cast
  ring

end Langlands.LocalFactor.RealTate
