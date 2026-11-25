import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Complex.Exponential

/-! # The radial Gaussian as a Schwartz function

`radialGaussian : 𝓢(E, ℝ)` is `x ↦ exp (-‖x‖²)` on a real inner product space `E`. The
definition keeps the full name under which it was first declared, in
`Langlands.Global.RankinSelberg.ComplexGodementGaussianPolynomial`; it stands in a file of its
own so that it can be imported without the global Rankin–Selberg theory.
-/

noncomputable section

open scoped ContDiff SchwartzMap

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodementGaussianPolynomial

/-- `r ^ k e ^ {-b r²} ≤ C e ^ {-b r² / 2}` for `r ≥ 0`. -/
private lemma exists_pow_mul_exp_neg_le (k : ℕ) {b : ℝ} (hb : 0 < b) :
    ∃ C, 0 < C ∧ ∀ r : ℝ, 0 ≤ r →
      r ^ k * Real.exp (-(b * r ^ 2)) ≤ C * Real.exp (-(b / 2 * r ^ 2)) := by
  refine ⟨1 + k.factorial * (2 / b) ^ k, by positivity, fun r hr => ?_⟩
  have hsplit : Real.exp (-(b * r ^ 2)) =
      Real.exp (-(b / 2 * r ^ 2)) * Real.exp (-(b / 2 * r ^ 2)) := by
    rw [← Real.exp_add]; ring_nf
  rw [hsplit, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  have hE : 1 ≤ Real.exp (b / 2 * r ^ 2) := Real.one_le_exp (by positivity)
  have hfac := Real.pow_div_factorial_le_exp (x := b / 2 * r ^ 2) (by positivity) k
  have hk : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  have h2 : r ^ (2 * k) ≤ k.factorial * (2 / b) ^ k * Real.exp (b / 2 * r ^ 2) := by
    rw [div_le_iff₀ hk, mul_pow] at hfac
    have : r ^ (2 * k) = (2 / b) ^ k * ((b / 2) ^ k * (r ^ 2) ^ k) := by
      rw [← mul_assoc, ← mul_pow, div_mul_div_comm, mul_comm 2 b, div_self (by positivity),
        one_pow, one_mul, ← pow_mul]
    rw [this]
    calc (2 / b) ^ k * ((b / 2) ^ k * (r ^ 2) ^ k)
        ≤ (2 / b) ^ k * (Real.exp (b / 2 * r ^ 2) * k.factorial) :=
          mul_le_mul_of_nonneg_left hfac (by positivity)
      _ = _ := by ring
  have hrk : r ^ k ≤ 1 + r ^ (2 * k) := by
    rcases le_total r 1 with h1 | h1
    · have := pow_le_one₀ hr h1 (n := k)
      linarith [pow_nonneg hr (2 * k)]
    · have := pow_le_pow_right₀ h1 (show k ≤ 2 * k by omega)
      linarith
  have hexp_inv : Real.exp (-(b / 2 * r ^ 2)) * Real.exp (b / 2 * r ^ 2) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  calc r ^ k * Real.exp (-(b / 2 * r ^ 2))
      ≤ (1 + r ^ (2 * k)) * Real.exp (-(b / 2 * r ^ 2)) :=
        mul_le_mul_of_nonneg_right hrk (Real.exp_pos _).le
    _ ≤ (Real.exp (b / 2 * r ^ 2) + k.factorial * (2 / b) ^ k * Real.exp (b / 2 * r ^ 2)) *
          Real.exp (-(b / 2 * r ^ 2)) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        linarith
    _ = 1 + k.factorial * (2 / b) ^ k := by
        have : (Real.exp (b / 2 * r ^ 2) + k.factorial * (2 / b) ^ k * Real.exp (b / 2 * r ^ 2)) *
            Real.exp (-(b / 2 * r ^ 2)) =
            (1 + k.factorial * (2 / b) ^ k) *
              (Real.exp (-(b / 2 * r ^ 2)) * Real.exp (b / 2 * r ^ 2)) := by ring
        rw [this, hexp_inv, mul_one]

/-- Gaussian decay implies polynomial decay of any order: `e ^ {-c u²} ≤ C (1 + u) ^ {-r}`. -/
private lemma exists_exp_neg_mul_sq_le_rpow {c : ℝ} (hc : 0 < c) (r : ℝ) :
    ∃ C, 0 < C ∧ ∀ u : ℝ, 0 ≤ u → Real.exp (-(c * u ^ 2)) ≤ C * (1 + u) ^ (-r) := by
  obtain ⟨k, hk⟩ := exists_nat_ge r
  obtain ⟨C, hC, hCb⟩ := exists_pow_mul_exp_neg_le k (show 0 < c / 2 by positivity)
  refine ⟨Real.exp c * C, by positivity, fun u hu => ?_⟩
  have hv : 1 ≤ 1 + u := by linarith
  have hv0 : 0 < 1 + u := by linarith
  have hsq : -(c * u ^ 2) ≤ c + -(c / 2 * (1 + u) ^ 2) := by nlinarith [sq_nonneg (u - 1)]
  have h1 : Real.exp (-(c * u ^ 2)) ≤ Real.exp c * Real.exp (-(c / 2 * (1 + u) ^ 2)) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr hsq
  have h2 := hCb (1 + u) hv0.le
  have h3 : Real.exp (-(c / 2 * (1 + u) ^ 2)) ≤ C * ((1 + u) ^ k)⁻¹ := by
    have hpos : 0 < (1 + u) ^ k := by positivity
    rw [le_mul_inv_iff₀ hpos]
    calc Real.exp (-(c / 2 * (1 + u) ^ 2)) * (1 + u) ^ k
        = (1 + u) ^ k * Real.exp (-(c / 2 * (1 + u) ^ 2)) := mul_comm _ _
      _ ≤ C * Real.exp (-(c / 2 / 2 * (1 + u) ^ 2)) := h2
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left
          (Real.exp_le_one_iff.mpr (by have := sq_nonneg (1 + u); nlinarith)) hC.le
      _ = C := mul_one C
  have h4 : ((1 + u) ^ k)⁻¹ ≤ (1 + u) ^ (-r) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg hv0.le]
    exact Real.rpow_le_rpow_of_exponent_le hv (by linarith)
  calc Real.exp (-(c * u ^ 2)) ≤ Real.exp c * Real.exp (-(c / 2 * (1 + u) ^ 2)) := h1
    _ ≤ Real.exp c * (C * ((1 + u) ^ k)⁻¹) := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ ≤ Real.exp c * (C * (1 + u) ^ (-r)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 hC.le) (by positivity)
    _ = Real.exp c * C * (1 + u) ^ (-r) := by ring

/-- The radial Gaussian on a real inner product space. -/
def radialGaussian {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] : 𝓢(E, ℝ) where
  toFun x := Real.exp (-‖x‖ ^ 2)
  smooth' := Real.contDiff_exp.comp <| (show (fun x : E => -‖x‖ ^ 2).HasTemperateGrowth by
    fun_prop).1
  decay' k n := by
    let Q : E → ℝ := fun x => -‖x‖ ^ 2
    have hQ : Q.HasTemperateGrowth := by dsimp [Q]; fun_prop
    obtain ⟨l, C, _, hderiv⟩ := hQ.norm_iteratedFDeriv_le_uniform n
    obtain ⟨B, _, hgauss⟩ := exists_exp_neg_mul_sq_le_rpow (c := 1)
      one_pos ((k + l * n : ℕ) : ℝ)
    let A := max 1 C
    refine ⟨(n.factorial : ℝ) * A ^ n * B, fun x => ?_⟩
    let R := 1 + ‖x‖
    have hR : 1 ≤ R := le_add_of_nonneg_right (norm_nonneg x)
    have hA : 1 ≤ A := le_max_left _ _
    have hD : 1 ≤ A * R ^ l := one_le_mul_of_one_le_of_one_le hA (one_le_pow₀ hR)
    have hbound := norm_iteratedFDeriv_comp_le (g := Real.exp) (f := Q) (n := n)
      Real.contDiff_exp hQ.1 (by exact_mod_cast le_top) x
      (C := Real.exp (Q x)) (D := A * R ^ l)
      (fun i _ => by
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate,
          Real.iter_deriv_exp, Real.norm_eq_abs, Real.abs_exp])
      (fun i hi hin => (hderiv i hin x).trans <|
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)).trans
          (le_self_pow₀ hD (by omega)))
    have hdecay : R ^ (k + l * n) * Real.exp (Q x) ≤ B := by
      have h := hgauss ‖x‖ (norm_nonneg x)
      simp only [one_mul] at h
      change Real.exp (Q x) ≤ B * R ^ (-((k + l * n : ℕ) : ℝ)) at h
      rw [Real.rpow_neg (by positivity), Real.rpow_natCast, le_mul_inv_iff₀ (by positivity)] at h
      rwa [mul_comm]
    change ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (Real.exp ∘ Q) x‖ ≤ _
    calc
      _ ≤ R ^ k * ((n.factorial : ℝ) * Real.exp (Q x) * (A * R ^ l) ^ n) := by
            gcongr
            exact le_add_of_nonneg_left zero_le_one
      _ = (n.factorial : ℝ) * A ^ n * (R ^ (k + l * n) * Real.exp (Q x)) := by
        rw [mul_pow, ← pow_mul, pow_add]
        ring
      _ ≤ (n.factorial : ℝ) * A ^ n * B := mul_le_mul_of_nonneg_left hdecay (by positivity)

end Langlands.Global.RankinSelbergGlobal.ComplexGodementGaussianPolynomial
