import Langlands.Global.RankinSelberg.RealRankZeroNormalization
import Langlands.Global.RankinSelberg.ArchimedeanGammaBounds
import Langlands.Global.RankinSelberg.OrdinarySemilocalNormalization
import Langlands.Automorphic.AssociatedGammaCuspidalEquation
import Langlands.LocalFactor.Archimedean.GammaStripGrowth

/-! # Exponential strip growth for the real rank-one ordinary local integral -/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped SchwartzMap FourierTransform Topology

set_option autoImplicit false

namespace Langlands.LocalFactor.RealTate

open Langlands.Global.RankinSelbergGlobal.ArchimedeanInverseMellin
open Langlands.LocalFactor.Archimedean

private theorem norm_integrand (f : ℝ → ℂ) (e : Fin 2) (s : ℂ) {x : ℝ} (hx : x ≠ 0) :
    ‖integrand f e s x‖ = ‖f x‖ * |x| ^ (s.re - 1) := by
  simp [integrand, hx, norm_pow, norm_real, Real.norm_eq_abs, abs_abs,
    norm_cpow_eq_rpow_re_of_pos (abs_pos.mpr hx), sub_re]

private theorem norm_zeta_on_strip (f : 𝓢(ℝ, ℂ)) (e : Fin 2) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖zeta f e s‖ ≤ C := by
  let M (x : ℝ) := ‖integrand f e (a : ℂ) x‖ + ‖integrand f e (b : ℂ) x‖
  have hM : Integrable M := ((integrable_integrand f e (by simpa only [ofReal_re] using ha)).norm).add
    ((integrable_integrand f e (by simpa only [ofReal_re] using hb)).norm)
  refine ⟨∫ x, M x, integral_nonneg (fun x => add_nonneg (norm_nonneg _) (norm_nonneg _)),
    fun s hs hs' => ?_⟩
  exact norm_integral_le_of_norm_le hM (Eventually.of_forall fun x => by
    by_cases hx : x = 0
    · subst x
      simp [M, integrand_zero]
    · simp only [M, norm_integrand f e _ hx, ofReal_re, ← mul_add]
      exact mul_le_mul_of_nonneg_left
        (rpow_le_add (abs_pos.mpr hx) (sub_le_sub_right hs 1) (sub_le_sub_right hs' 1)) (norm_nonneg _))

private theorem norm_normalizedZeta_on_positive_strip (f : 𝓢(ℝ, ℂ)) (e : Fin 2) (b : ℝ) :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ b →
      ‖normalizedZeta f e s‖ ≤ C * Real.exp (K * |s.im|) := by
  obtain ⟨C, hC, hZ⟩ := norm_zeta_on_strip f e (a := 1 / 2) (b := max b 1) (by norm_num)
    (zero_lt_one.trans_le (le_max_right _ _))
  obtain ⟨G, K, hG, hK, hΓ⟩ := inv_Gammaℝ_stripExpType.comp_add (e.val : ℂ) (1 / 2) b
  refine ⟨C * G, K, mul_nonneg hC hG, hK, fun s hlo hhi => ?_⟩
  have hs : 0 < s.re := (by norm_num : 0 < (1 / 2 : ℝ)).trans_le hlo
  rw [normalizedZeta_eq_right f e hs, norm_mul, mul_assoc]
  have hg := hΓ s.re hlo hhi s.im
  rw [re_add_im] at hg
  exact mul_le_mul (hZ s hlo (hhi.trans (le_max_left _ _))) hg (norm_nonneg _) hC

private theorem normalizedZeta_eq_left (f : 𝓢(ℝ, ℂ)) (e : Fin 2) {u : ℂ} (h₁ : u.re < 1) :
    normalizedZeta f e u = (I ^ e.val)⁻¹ * zeta (𝓕⁻ f : 𝓢(ℝ, ℂ)) e (1 - u) *
      (Gammaℝ (1 - u + (e.val : ℂ)))⁻¹ := by
  by_cases h₀ : 0 < u.re
  · rw [normalizedZeta_eq_right f e h₀]
    have hg₀ := Gammaℝ_ne_zero_of_re_pos (re_add_pos h₀ e)
    have hg₁ := Gammaℝ_ne_zero_of_re_pos (re_one_sub_add_pos h₁ e)
    have hi : I ^ e.val ≠ 0 := pow_ne_zero _ I_ne_zero
    field_simp [hg₀, hg₁, hi]
    linear_combination -(zeta_fourierInv_mul_Gammaℝ f e h₀ h₁)
  · rw [normalizedZeta, ite_eq_right h₀]
    rfl

/-- The entire normalized real Tate integral has exponential growth in vertical strips. -/
theorem stripGrowth_normalizedZeta (f : 𝓢(ℝ, ℂ)) (e : Fin 2) :
    HasStripExponentialGrowth (normalizedZeta f e) := by
  intro a b
  obtain ⟨C, K, hC, hK, hR⟩ := norm_normalizedZeta_on_positive_strip f e b
  obtain ⟨D, L, hD, hL, hLbound⟩ := norm_normalizedZeta_on_positive_strip (𝓕⁻ f) e (1 - a)
  refine ⟨max C D, max K L, 0, hC.trans (le_max_left _ _), hK.trans (le_max_left _ _),
    fun s ha hb _ => ?_⟩
  by_cases h : 1 / 2 ≤ s.re
  · exact (hR s h hb).trans (mul_le_mul (le_max_left _ _) (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))) (Real.exp_pos _).le
      (hC.trans (le_max_left _ _)))
  · have h₁ : s.re < 1 := (lt_of_not_ge h).trans (by norm_num)
    have h₀ : 0 < (1 - s).re := by simp [sub_re, h₁]
    have hrev : 1 / 2 ≤ (1 - s).re := by
      rw [sub_re, one_re]
      linarith [lt_of_not_ge h]
    have hrev' : (1 - s).re ≤ 1 - a := by
      simpa only [sub_re, one_re] using sub_le_sub_left ha 1
    have hnorm : ‖normalizedZeta f e s‖ = ‖normalizedZeta (𝓕⁻ f : 𝓢(ℝ, ℂ)) e (1 - s)‖ := by
      rw [normalizedZeta_eq_left f e h₁, normalizedZeta_eq_right _ _ h₀]
      simp [norm_inv, norm_pow]
    have hbound := hLbound (1 - s) hrev hrev'
    rw [← hnorm, sub_im, one_im, zero_sub, abs_neg] at hbound
    exact hbound.trans (mul_le_mul (le_max_right _ _) (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _))) (Real.exp_pos _).le
      (hC.trans (le_max_left _ _)))

end Langlands.LocalFactor.RealTate

namespace Langlands.Global.RankinSelbergGlobal.RealRankZero

open LocalFactor LocalFactor.Archimedean ArchimedeanLocal
open FunctionalEquationComparison.CompletedEquationAdapter (realPairLFactor_denominator_ne_zero)

attribute [local instance] archimedeanRealGLMeasurable archimedeanRealGLBorel
  archimedeanRealNMeasurable archimedeanRealNBorel archimedeanRealQMeasurable
  archimedeanRealQBorel

/-- The actual real rank-one ordinary integral of two character coefficients has an entire
normalization of exponential strip growth. -/
def RealRankZeroStripGrowthStatement : Prop :=
  ∀ (D : RealQuotientMeasureData 0) (c c' : RealCharacterData)
    (W W' : Langlands.GeneralLinear (0 + 1) ℝ → ℂ) (C C' : ℂ),
    (∀ g, W g = C * (c.character (GeneralLinear.determinant g) : ℂ)) →
    (∀ g, W' g = C' * (c'.character (GeneralLinear.determinant g) : ℂ)) →
    ∀ Φ : 𝓢(Fin (0 + 1) → ℝ, ℂ),
    ∃ N : OrdinaryIntegralNormalization (realEqualIntegral D W W' Φ)
      (fun s => ((realPairLFactor [.character c] [.character c']).denominator s)⁻¹),
      HasStripExponentialGrowth N.value

theorem realRankZeroStripGrowth : RealRankZeroStripGrowthStatement := by
  intro D c c' W W' C C' hW hW' Φ
  obtain ⟨κ, _, hκ⟩ := exists_measure_eq (D := D)
  obtain ⟨τ, hτ⟩ := realPairLFactor_denominator_ne_zero [.character c] [.character c']
  let d := c.mul c'
  let α : ℂ := (κ : ℂ) * (C * C')
  let N (s : ℂ) := α * RealTate.normalizedZeta (lineSchwartz Φ) d.parity (s + d.exponent)
  have hN (s : ℂ) : AnalyticAt ℂ N s := by
    have h := (RealTate.analyticAt_normalizedZeta (lineSchwartz Φ) d.parity (s + d.exponent)).comp
      (f := fun w : ℂ => w + d.exponent) (x := s) (by fun_prop)
    exact analyticAt_const.fun_mul h
  have hG : HasStripExponentialGrowth N := by
    have hg : HasStripExponentialGrowth (fun s => RealTate.normalizedZeta (lineSchwartz Φ) d.parity
        (s + d.exponent)) := by
      simpa only [ofReal_one, div_one] using
        (RealTate.stripGrowth_normalizedZeta (lineSchwartz Φ) d.parity).div_add d.exponent
          (c := 1) one_pos
    intro a b
    obtain ⟨B, K, T, hB, hK, hg⟩ := hg a b
    refine ⟨‖α‖ * B, K, T, by positivity, hK, fun s ha hb hs => ?_⟩
    dsimp only [N]
    rw [norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hg s ha hb hs) (norm_nonneg _)
  refine ⟨⟨N, fun s _ => hN s, ⟨max τ (-d.exponent.re), fun s hs => ?_⟩⟩, hG⟩
  have hpos : 0 < (s + d.exponent).re := by
    rw [add_re]
    linarith [(le_max_right τ (-d.exponent.re)).trans_lt hs]
  have hD := hτ s ((le_max_left τ (-d.exponent.re)).trans_lt hs)
  have hEq : N s = realEqualIntegral D W W' Φ s *
      (realPairLFactor [.character c] [.character c']).denominator s := by
    dsimp only [N, α, d]
    rw [RealTate.normalizedZeta_eq_right _ _ hpos, equalIntegral_eq c c' hκ hW hW',
      realPairLFactor_character, ← add_assoc]
    ring
  rw [hEq, mul_assoc, mul_inv_cancel₀ hD, mul_one]

end Langlands.Global.RankinSelbergGlobal.RealRankZero
