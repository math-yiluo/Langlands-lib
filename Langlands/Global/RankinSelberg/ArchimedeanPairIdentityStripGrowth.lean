import Langlands.Global.RankinSelberg.ArchimedeanRealPairIdentity
import Langlands.Global.RankinSelberg.ArchimedeanMellinPairStripGrowth

/-! # Exponential strip growth from Jacquet's pair identity -/

noncomputable section

open Filter MeasureTheory Set

set_option autoImplicit false

universe u v

namespace Langlands.Global.RankinSelbergGlobal.ArchimedeanRealPairIdentity

open ArchimedeanInverseMellin ArchimedeanMellinPair
open LocalFactor LocalFactor.Archimedean

private theorem stripExpType_of_norm_re {E : ℂ → ℂ} (hE : Continuous E)
    (hEn : ∀ s : ℂ, ‖E s‖ = ‖E (s.re : ℂ)‖) : StripExpType E := by
  intro a b
  obtain ⟨C, hC⟩ := (isCompact_Icc.image (hE.comp Complex.continuous_ofReal).norm
    (s := Icc a b)).bddAbove
  refine ⟨max C 0, 0, le_max_right _ _, le_rfl, fun x ha hb y => ?_⟩
  rw [hEn, Complex.add_re, Complex.mul_I_re, Complex.ofReal_im, neg_zero, add_zero,
    Complex.ofReal_re, zero_mul, Real.exp_zero, mul_one]
  exact (hC (mem_image_of_mem (fun z : ℝ => ‖E (z : ℂ)‖) ⟨ha, hb⟩)).trans (le_max_left _ _)

private theorem stripGrowth_of_stripExpType {D : ℂ → ℂ} (hD : StripExpType D) :
    HasStripExponentialGrowth D := by
  intro a b
  obtain ⟨C, K, hC, hK, hbound⟩ := hD a b
  refine ⟨C, K, 0, hC, hK, fun s ha hb _ => ?_⟩
  simpa only [Complex.re_add_im] using hbound s.re ha hb s.im

private theorem weighted_kernel_of_convergence {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {K : ℂ → X → ℂ} {δ : X → ℝ}
    (hδm : Measurable δ) (hδ : ∀ x, 0 < δ x)
    (hK : ∀ s x, K s x = K 0 x * (δ x : ℂ) ^ s)
    {σ₀ : ℝ} (hKi : ∀ s : ℂ, σ₀ < s.re → Integrable (K s) μ) :
    AEStronglyMeasurable (K 0) μ ∧
      ∀ σ : ℝ, σ₀ + 1 ≤ σ → Integrable (fun x => ‖K 0 x‖ * δ x ^ σ) μ := by
  let z : ℂ := (σ₀ + 1 : ℝ)
  have hz : σ₀ < z.re := by simp [z]
  constructor
  · have hm : Measurable fun x => (δ x : ℂ) ^ (-z) :=
      (Complex.measurable_ofReal.comp hδm).pow_const _
    exact ((hKi z hz).aestronglyMeasurable.mul hm.aestronglyMeasurable).congr
      (Eventually.of_forall fun x => (kernel_zero_eq hδ hK z x).symm)
  · intro σ hσ
    have hlt : σ₀ < ((σ : ℝ) : ℂ).re := by simp only [Complex.ofReal_re]; linarith
    exact (hKi _ hlt).norm.congr (Eventually.of_forall fun x => norm_kernel hδ hK σ x)

/-- The pair identity gives an entire normalization of exponential strip growth for
kernels with positive determinant powers and a common right convergence half-plane. -/
def PairIdentityNormalizedStripGrowthStatement : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (K : ℂ → X → ℂ) (Kd : ℂ → Y → ℂ) (δ : X → ℝ) (δd : Y → ℝ)
    (σ₀ : ℝ) (L Ld : ReciprocalEntire) (E : ℂ → ℂ) (sign : ℂ),
    Measurable δ → Measurable δd → (∀ x, 0 < δ x) → (∀ y, 0 < δd y) →
    (∀ s x, K s x = K 0 x * (δ x : ℂ) ^ s) →
    (∀ s y, Kd s y = Kd 0 y * (δd y : ℂ) ^ s) →
    (∀ s : ℂ, σ₀ < s.re → Integrable (K s) μ) →
    (∀ s : ℂ, σ₀ < s.re → Integrable (Kd s) ν) →
    StripExpType L.denominator → StripExpType Ld.denominator →
    (∃ τ : ℝ, ∀ s : ℂ, τ < s.re → L.denominator s ≠ 0 ∧ Ld.denominator s ≠ 0) →
    Differentiable ℂ E → (∀ s : ℂ, E s ≠ 0) → (∀ s : ℂ, ‖E s‖ = ‖E (s.re : ℂ)‖) →
    sign ≠ 0 → PairIdentity μ ν (K 0) δ (Kd 0) δd L.denominator Ld.denominator E sign →
    ∃ R : OrdinaryIntegralNormalization (fun s => ∫ x, K s x ∂μ) (fun s => (L.denominator s)⁻¹),
      HasStripExponentialGrowth R.value

theorem pairIdentityNormalizedStripGrowth : PairIdentityNormalizedStripGrowthStatement.{u, v} := by
  intro X Y _ _ μ ν _ _ K Kd δ δd σ₀ L Ld E sign hδm hδdm hδ hδd hK hKd hKi hKdi
    hLt hLdt hne hEa hEne hEn hsign hpair
  obtain ⟨τ, hτ⟩ := hne
  obtain ⟨h, k, hh, hk, hhd, hkd, hhM, hkM, _, _, _⟩ :=
    exists_factor_pair L.entire Ld.entire hEa hLt hLdt (stripExpType_of_norm_re hEa.continuous hEn)
      hsign (σ₀ := τ) (fun s hs => ⟨(hτ s hs).1, (hτ s hs).2, hEne s⟩)
  obtain ⟨hF, hFN⟩ := weighted_kernel_of_convergence hδm hδ hK hKi
  obtain ⟨hG, hGN⟩ := weighted_kernel_of_convergence hδdm hδd hKd hKdi
  let Einv (s : ℂ) := (sign * E s)⁻¹
  have hEinv : Differentiable ℂ Einv := by
    intro s
    exact (hEa.differentiableAt.const_mul sign).inv (mul_ne_zero hsign (hEne s))
  have hEinvn (s : ℂ) : ‖Einv s‖ = ‖Einv (s.re : ℂ)‖ := by
    simp only [Einv, norm_inv, norm_mul, hEn s]
  have hθ (a : ℝ) (ha : 0 < a) := theta_eq_of_pairIdentity hpair hh hk hhd hkd hhM hkM ha
  have hMh (s : ℂ) : Einv s * mellin h (-s) = Complex.exp (s ^ 2) * L.denominator s := by
    dsimp only [Einv]
    rw [hhM, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (mul_ne_zero hsign (hEne s)), one_mul]
  obtain ⟨R, hR⟩ := mellinPairNormalizedStripGrowth μ ν (K 0) δ (Kd 0) δd h k (σ₀ + 1)
    L Ld Einv hF hG hδm hδdm hδ hδd hh hk hhd hkd hFN hGN hθ hMh hkM hEinv hEinvn
    (stripGrowth_of_stripExpType hLt) (stripGrowth_of_stripExpType hLdt) ⟨τ, fun s hs => (hτ s hs).1⟩
  refine ⟨⟨R.value, R.analytic, ?_⟩, hR⟩
  obtain ⟨b, hb⟩ := R.eq_on_right
  refine ⟨b, fun s hs => ?_⟩
  rw [integral_congr_ae (Eventually.of_forall (hK s))]
  exact hb s hs

end Langlands.Global.RankinSelbergGlobal.ArchimedeanRealPairIdentity
