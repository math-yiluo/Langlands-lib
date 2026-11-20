import Langlands.Global.RankinSelberg.ComplexRankZeroLocal
import Langlands.LocalFactor.Archimedean.ComplexTateProof

/-! # Entire normalized ordinary integrals for complex `GL₁ × GL₁` -/

noncomputable section

set_option autoImplicit false

open Complex Filter Set Topology
open scoped SchwartzMap

namespace Langlands.LocalFactor.ComplexTate

private def gammaShift (m : ℤ) : ℂ := (m.natAbs : ℂ) / 2

private def normalizedRight (f : 𝓢(ℂ, ℂ)) (m : ℤ) (u : ℂ) : ℂ :=
  zeta f m u * (Gammaℂ (u + gammaShift m))⁻¹

private def normalizedLeft (f : 𝓢(ℂ, ℂ)) (m : ℤ) (u : ℂ) : ℂ :=
  (I ^ m.natAbs)⁻¹ * zeta (fourier f) (-m) (1 - u) * (Gammaℂ (1 - u + gammaShift m))⁻¹

private theorem one_sub_re_pos {u : ℂ} (hu : u.re < 1) : 0 < (1 - u).re := by
  rw [sub_re, one_re]
  exact sub_pos.mpr hu

private theorem gammaShift_ne_zero (m : ℤ) {u : ℂ} (hu : 0 < u.re) :
    Gammaℂ (u + gammaShift m) ≠ 0 := by
  rw [Gammaℂ_def]
  have hπ : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hshift : 0 < (u + gammaShift m).re := by
    simp only [gammaShift, add_re, div_ofNat_re, natCast_re]
    positivity
  exact mul_ne_zero (mul_ne_zero two_ne_zero (cpow_ne_zero_iff.mpr (Or.inl hπ)))
    (Gamma_ne_zero_of_re_pos hshift)

private theorem normalizedRight_eq_left (f : 𝓢(ℂ, ℂ)) (m : ℤ) {u : ℂ}
    (hu : 0 < u.re) (hu' : u.re < 1) : normalizedRight f m u = normalizedLeft f m u := by
  have hg : (gaussSchwartz m : ℂ → ℂ) = gaussian m := funext (gaussSchwartz_apply m)
  have hfg : (fourier (gaussSchwartz m) : ℂ → ℂ) = fun y => I ^ m.natAbs * gaussian (-m) y := by
    funext y
    simpa only [fourier_apply, hg, traceChar] using integral_exp_mul_gaussian m y
  have h := tate_identity f (gaussSchwartz m) m hu hu'
  simp only [hg, hfg, zeta_const_mul, zeta_gaussian m hu,
    zeta_gaussian (-m) (one_sub_re_pos hu'), Int.natAbs_neg] at h
  unfold normalizedRight normalizedLeft
  field_simp [gammaShift_ne_zero m hu, gammaShift_ne_zero m (one_sub_re_pos hu'),
    pow_ne_zero m.natAbs I_ne_zero]
  unfold gammaShift
  linear_combination h

/-- The complex Tate integral normalized by the Gamma factor, continued using the
reflected Tate integral on the left half-plane. -/
def normalizedZeta (f : 𝓢(ℂ, ℂ)) (m : ℤ) (u : ℂ) : ℂ :=
  if 0 < u.re then normalizedRight f m u else normalizedLeft f m u

/-- On the original half-plane this is the zeta integral times the Gamma denominator. -/
theorem normalizedZeta_eq_right (f : 𝓢(ℂ, ℂ)) (m : ℤ) {u : ℂ} (hu : 0 < u.re) :
    normalizedZeta f m u = zeta f m u * (Gammaℂ (u + (m.natAbs : ℂ) / 2))⁻¹ := by
  simp [normalizedZeta, hu, normalizedRight, gammaShift]

/-- The normalized complex Tate integral is entire. -/
theorem analyticAt_normalizedZeta (f : 𝓢(ℂ, ℂ)) (m : ℤ) (u : ℂ) :
    AnalyticAt ℂ (normalizedZeta f m) u := by
  by_cases hu : 0 < u.re
  · have hden : AnalyticAt ℂ (fun w => (Gammaℂ (w + (m.natAbs : ℂ) / 2))⁻¹) u :=
      (differentiable_Gammaℂ_inv.analyticAt _).comp (by fun_prop)
    refine ((analyticAt_zeta f m hu).fun_mul hden).congr ?_
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hu] with w hw
    exact (normalizedZeta_eq_right f m hw).symm
  · have hu' : u.re < 1 := lt_of_le_of_lt (le_of_not_gt hu) zero_lt_one
    have hz : AnalyticAt ℂ (fun w => zeta (fourier f) (-m) (1 - w)) u :=
      (analyticAt_zeta (fourier f) (-m) (one_sub_re_pos hu')).comp (by fun_prop)
    have hden : AnalyticAt ℂ (fun w => (Gammaℂ (1 - w + gammaShift m))⁻¹) u :=
      (differentiable_Gammaℂ_inv.analyticAt _).comp (by fun_prop)
    refine ((analyticAt_const.fun_mul hz).fun_mul hden : AnalyticAt ℂ (normalizedLeft f m) u).congr ?_
    filter_upwards [(isOpen_lt continuous_re continuous_const).mem_nhds hu'] with w hw
    by_cases h : 0 < w.re
    · simp only [normalizedZeta, ite_eq_left h, normalizedRight_eq_left f m h hw, normalizedLeft]
    · simp only [normalizedZeta, ite_eq_right h, normalizedLeft]

/-- The angular Gaussian has normalized zeta integral one. -/
theorem normalizedZeta_gaussian (m : ℤ) : normalizedZeta (gaussSchwartz m) m = 1 := by
  have hg : AnalyticOnNhd ℂ (normalizedZeta (gaussSchwartz m) m) univ :=
    fun u _ => analyticAt_normalizedZeta _ _ u
  have h₁ : AnalyticOnNhd ℂ (1 : ℂ → ℂ) univ := fun _ _ => analyticAt_const
  apply hg.eq_of_eventuallyEq h₁ (z₀ := 1)
  filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num : 0 < (1 : ℂ).re)]
    with u hu
  rw [normalizedZeta_eq_right _ _ hu, funext (gaussSchwartz_apply m), zeta_gaussian m hu]
  exact mul_inv_cancel₀ (gammaShift_ne_zero m hu)

end Langlands.LocalFactor.ComplexTate

namespace Langlands.Global.RankinSelbergGlobal.ComplexRankZero

open Langlands.LocalFactor Langlands.LocalFactor.Archimedean ArchimedeanLocal

private theorem zeta_shift (f : ℂ → ℂ) (m : ℤ) (t s : ℂ) :
    ComplexTate.zeta f m t s = LocalFactor.ComplexTate.zeta f m (s + t) := rfl

/-- The actual ordinary integral of two complex characters is an entire multiple
of their pair L-factor, on the initial half-plane. -/
theorem exists_normalized_complexEqualIntegral (D : ComplexQuotientMeasureData 0)
    (c c' : ComplexCharacterData) {W W' : Langlands.GeneralLinear (0 + 1) ℂ → ℂ} {C C' : ℂ}
    (hW : ∀ g, W g = C * (c.character (GeneralLinear.determinant g) : ℂ))
    (hW' : ∀ g, W' g = C' * (c'.character (GeneralLinear.determinant g) : ℂ))
    (Φ : 𝓢(Fin (0 + 1) → ℂ, ℂ)) :
    ∃ N : ℂ → ℂ, AnalyticOnNhd ℂ N univ ∧ ∀ s, 0 < (s + (c.mul c').exponent).re →
      N s = complexEqualIntegral D W W' Φ s * (complexPairLFactor [c] [c']).denominator s := by
  obtain ⟨κ, _, hκ⟩ := exists_measure_eq D
  let d := c.mul c'
  let N (s : ℂ) : ℂ := (κ : ℂ) / 2 * (C * C') *
    LocalFactor.ComplexTate.normalizedZeta (lineSchwartz Φ) d.weight (s + d.exponent)
  refine ⟨N, fun s _ => ?_, fun s hs => ?_⟩
  · have h := (LocalFactor.ComplexTate.analyticAt_normalizedZeta
      (lineSchwartz Φ) d.weight (s + d.exponent)).comp
      (f := fun w : ℂ => w + d.exponent) (x := s) (by fun_prop)
    exact analyticAt_const.fun_mul h
  · unfold N d
    rw [LocalFactor.ComplexTate.normalizedZeta_eq_right _ _ hs,
      equalIntegral_eq c c' hκ hW hW', zeta_shift, complexPairLFactor_singleton, ← add_assoc]
    ring

/-- Nonzero rank-one Whittaker functions admit a Schwartz test realizing the
complex pair L-factor itself on the initial half-plane. -/
theorem exists_complexEqualIntegral_eq_LFactor (D : ComplexQuotientMeasureData 0)
    (c c' : ComplexCharacterData) {W W' : Langlands.GeneralLinear (0 + 1) ℂ → ℂ} {C C' : ℂ}
    (hW : ∀ g, W g = C * (c.character (GeneralLinear.determinant g) : ℂ))
    (hW' : ∀ g, W' g = C' * (c'.character (GeneralLinear.determinant g) : ℂ))
    (hC : C ≠ 0) (hC' : C' ≠ 0) :
    ∃ Φ : 𝓢(Fin (0 + 1) → ℂ, ℂ), ∀ s, 0 < (s + (c.mul c').exponent).re →
      complexEqualIntegral D W W' Φ s = ((complexPairLFactor [c] [c']).denominator s)⁻¹ := by
  let : Unique (Fin (0 + 1)) := inferInstanceAs (Unique (Fin 1))
  obtain ⟨κ, hκ0, hκ⟩ := exists_measure_eq D
  let a : ℂ := (κ : ℂ) / 2 * (C * C')
  have hκC : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ0
  have ha : a ≠ 0 := mul_ne_zero (div_ne_zero hκC two_ne_zero) (mul_ne_zero hC hC')
  let Ψ : 𝓢(ℂ, ℂ) := a⁻¹ • LocalFactor.ComplexTate.gaussSchwartz (c.mul c').weight
  let Φ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.funUnique (Fin (0 + 1)) ℝ ℂ) Ψ
  have hΦ : lineSchwartz Φ = Ψ := by
    ext z
    rw [lineSchwartz_apply]
    rfl
  have hΨ : (Ψ : ℂ → ℂ) = fun z => a⁻¹ * LocalFactor.ComplexTate.gaussian (c.mul c').weight z := by
    ext z
    simp [Ψ, smul_eq_mul, LocalFactor.ComplexTate.gaussSchwartz_apply]
  refine ⟨Φ, fun s hs => ?_⟩
  rw [equalIntegral_eq c c' hκ hW hW', hΦ, zeta_shift, hΨ,
    complexPairLFactor_singleton, inv_inv, ← add_assoc,
    LocalFactor.ComplexTate.zeta_const_mul, LocalFactor.ComplexTate.zeta_gaussian _ hs,
    ← mul_assoc, mul_inv_cancel₀ ha, one_mul]

end Langlands.Global.RankinSelbergGlobal.ComplexRankZero
