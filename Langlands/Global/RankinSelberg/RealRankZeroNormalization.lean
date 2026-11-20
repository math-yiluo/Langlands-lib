import Langlands.Global.RankinSelberg.RealRankZeroLocal
import Langlands.LocalFactor.Archimedean.RealTateProof

/-! # Entire normalized ordinary integrals for real `GL₁ × GL₁` -/

noncomputable section

set_option autoImplicit false

open Complex Filter Set Topology
open scoped SchwartzMap FourierTransform

namespace Langlands.LocalFactor.RealTate

private def normalizedRight (f : 𝓢(ℝ, ℂ)) (e : Fin 2) (u : ℂ) : ℂ :=
  zeta f e u * (Gammaℝ (u + (e.val : ℂ)))⁻¹

private def normalizedLeft (f : 𝓢(ℝ, ℂ)) (e : Fin 2) (u : ℂ) : ℂ :=
  (I ^ e.val)⁻¹ * zeta (𝓕⁻ f : 𝓢(ℝ, ℂ)) e (1 - u) * (Gammaℝ (1 - u + (e.val : ℂ)))⁻¹

private theorem normalizedRight_eq_left (f : 𝓢(ℝ, ℂ)) (e : Fin 2) {u : ℂ}
    (hu : 0 < u.re) (hu' : u.re < 1) : normalizedRight f e u = normalizedLeft f e u := by
  have hg₀ := Gammaℝ_ne_zero_of_re_pos (re_add_pos hu e)
  have hg₁ := Gammaℝ_ne_zero_of_re_pos (re_one_sub_add_pos hu' e)
  have hi : I ^ e.val ≠ 0 := pow_ne_zero _ I_ne_zero
  unfold normalizedRight normalizedLeft
  field_simp [hg₀, hg₁, hi]
  linear_combination -(zeta_fourierInv_mul_Gammaℝ f e hu hu')

/-- The two Tate integrals divided by their Gamma factors give the same
normalization in their common range of convergence. -/
def normalizedZeta (f : 𝓢(ℝ, ℂ)) (e : Fin 2) (u : ℂ) : ℂ :=
  if 0 < u.re then normalizedRight f e u else normalizedLeft f e u

/-- On the original half-plane this is the zeta integral times the Gamma denominator. -/
theorem normalizedZeta_eq_right (f : 𝓢(ℝ, ℂ)) (e : Fin 2) {u : ℂ} (hu : 0 < u.re) :
    normalizedZeta f e u = zeta f e u * (Gammaℝ (u + (e.val : ℂ)))⁻¹ := by
  simp [normalizedZeta, hu, normalizedRight]

/-- The normalized real Tate integral is entire. -/
theorem analyticAt_normalizedZeta (f : 𝓢(ℝ, ℂ)) (e : Fin 2) (u : ℂ) :
    AnalyticAt ℂ (normalizedZeta f e) u := by
  by_cases hu : 0 < u.re
  · have hden : AnalyticAt ℂ (fun w => (Gammaℝ (w + (e.val : ℂ)))⁻¹) u :=
      (differentiable_Gammaℝ_inv.analyticAt _).comp (by fun_prop)
    refine ((analyticAt_zeta f e hu).fun_mul hden).congr ?_
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hu] with w hw
    exact (normalizedZeta_eq_right f e hw).symm
  · have hu' : u.re < 1 := lt_of_le_of_lt (le_of_not_gt hu) zero_lt_one
    have hleft : 0 < (1 - u).re := by simp [sub_re, hu']
    have hz : AnalyticAt ℂ (fun w => zeta (𝓕⁻ f : 𝓢(ℝ, ℂ)) e (1 - w)) u :=
      (analyticAt_zeta (𝓕⁻ f : 𝓢(ℝ, ℂ)) e hleft).comp (by fun_prop)
    have hden : AnalyticAt ℂ (fun w => (Gammaℝ (1 - w + (e.val : ℂ)))⁻¹) u :=
      (differentiable_Gammaℝ_inv.analyticAt _).comp (by fun_prop)
    have hAnalytic : AnalyticAt ℂ (normalizedLeft f e) u :=
      (analyticAt_const.fun_mul hz).fun_mul hden
    refine hAnalytic.congr ?_
    filter_upwards [(isOpen_lt continuous_re continuous_const).mem_nhds hu'] with w hw
    by_cases h : 0 < w.re
    · simp only [normalizedZeta, ite_eq_left h, normalizedRight_eq_left f e h hw]
    · simp only [normalizedZeta, ite_eq_right h]

/-- The parity-adapted Gaussian has normalized zeta integral one. -/
theorem normalizedZeta_gaussian (e : Fin 2) : normalizedZeta (gaussSchwartzE e) e = 1 := by
  have hg : AnalyticOnNhd ℂ (normalizedZeta (gaussSchwartzE e) e) univ :=
    fun u _ => analyticAt_normalizedZeta _ _ u
  have h₁ : AnalyticOnNhd ℂ (1 : ℂ → ℂ) univ := fun _ _ => analyticAt_const
  apply hg.eq_of_eventuallyEq h₁ (z₀ := 1)
  filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num : 0 < (1 : ℂ).re)]
    with u hu
  rw [normalizedZeta_eq_right _ _ hu, zeta_gaussSchwartzE e hu,
    mul_inv_cancel₀ (Gammaℝ_ne_zero_of_re_pos (re_add_pos hu e))]
  rfl

end Langlands.LocalFactor.RealTate

namespace Langlands.Global.RankinSelbergGlobal.RealRankZero

open Langlands.LocalFactor Langlands.LocalFactor.Archimedean ArchimedeanLocal

/-- The actual ordinary integral of two real characters is an entire multiple
of their pair L-factor, on the initial half-plane. -/
theorem exists_normalized_realEqualIntegral (D : RealQuotientMeasureData 0)
    (c c' : RealCharacterData) {W W' : Langlands.GeneralLinear (0 + 1) ℝ → ℂ} {C C' : ℂ}
    (hW : ∀ g, W g = C * (c.character (GeneralLinear.determinant g) : ℂ))
    (hW' : ∀ g, W' g = C' * (c'.character (GeneralLinear.determinant g) : ℂ))
    (Φ : 𝓢(Fin (0 + 1) → ℝ, ℂ)) :
    ∃ N : ℂ → ℂ, AnalyticOnNhd ℂ N univ ∧ ∀ s, 0 < (s + (c.mul c').exponent).re →
      N s = realEqualIntegral D W W' Φ s *
        (realPairLFactor [RealBlock.character c] [RealBlock.character c']).denominator s := by
  obtain ⟨κ, _, hκ⟩ := exists_measure_eq (D := D)
  let d := c.mul c'
  let N (s : ℂ) : ℂ := (κ : ℂ) * (C * C') *
    RealTate.normalizedZeta (lineSchwartz Φ) d.parity (s + d.exponent)
  refine ⟨N, fun s _ => ?_, fun s hs => ?_⟩
  · have h := (RealTate.analyticAt_normalizedZeta (lineSchwartz Φ) d.parity (s + d.exponent)).comp
      (f := fun w : ℂ => w + d.exponent) (x := s) (by fun_prop)
    exact analyticAt_const.fun_mul h
  · unfold N d
    rw [RealTate.normalizedZeta_eq_right _ _ hs, equalIntegral_eq c c' hκ hW hW',
      realPairLFactor_character, ← add_assoc]
    ring

/-- Nonzero rank-one Whittaker functions admit a Schwartz test realizing the
real pair L-factor itself on the initial half-plane. -/
theorem exists_realEqualIntegral_eq_LFactor (D : RealQuotientMeasureData 0)
    (c c' : RealCharacterData) {W W' : Langlands.GeneralLinear (0 + 1) ℝ → ℂ} {C C' : ℂ}
    (hW : ∀ g, W g = C * (c.character (GeneralLinear.determinant g) : ℂ))
    (hW' : ∀ g, W' g = C' * (c'.character (GeneralLinear.determinant g) : ℂ))
    (hC : C ≠ 0) (hC' : C' ≠ 0) :
    ∃ Φ : 𝓢(Fin (0 + 1) → ℝ, ℂ), ∀ s, 0 < (s + (c.mul c').exponent).re →
      realEqualIntegral D W W' Φ s =
        ((realPairLFactor [RealBlock.character c] [RealBlock.character c']).denominator s)⁻¹ := by
  classical
  let : Unique (Fin (0 + 1)) := inferInstanceAs (Unique (Fin 1))
  obtain ⟨κ, hκ0, hκ⟩ := exists_measure_eq (D := D)
  let a : ℂ := (κ : ℂ) * (C * C')
  have hκC : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ0
  have ha : a ≠ 0 := mul_ne_zero hκC (mul_ne_zero hC hC')
  let Ψ : 𝓢(ℝ, ℂ) := a⁻¹ • RealTate.gaussSchwartzE (c.mul c').parity
  let Φ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.funUnique (Fin (0 + 1)) ℝ ℝ) Ψ
  have hΦ : lineSchwartz Φ = Ψ := by
    ext x
    rw [lineSchwartz_apply]
    rfl
  refine ⟨Φ, fun s hs => ?_⟩
  rw [equalIntegral_eq c c' hκ hW hW', hΦ, realPairLFactor_character, inv_inv, ← add_assoc,
    ← mul_assoc]
  have hΨ : (Ψ : ℝ → ℂ) = fun x => a⁻¹ * RealTate.gaussSchwartzE (c.mul c').parity x := by
    ext x
    simp [Ψ, smul_eq_mul]
  rw [hΨ]
  rw [RealTate.zeta_const_mul, RealTate.zeta_gaussSchwartzE _ hs, ← mul_assoc,
    mul_inv_cancel₀ ha, one_mul]

end Langlands.Global.RankinSelbergGlobal.RealRankZero
