import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! # Plancherel in real coordinates with positive phase -/

noncomputable section

set_option autoImplicit false

open MeasureTheory SchwartzMap
open scoped ComplexInnerProductSpace ENNReal FourierTransform

namespace Langlands.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

/-- The Fourier integral agrees almost everywhere with the `L²` Fourier transform
when both constructions apply. -/
theorem ae_fourier_toLp_eq {f : E → ℂ} (h₁ : Integrable f) (h₂ : MemLp f 2) :
    ((𝓕 (h₂.toLp f) : Lp ℂ 2 (volume : Measure E)) : E → ℂ) =ᵐ[volume] 𝓕 f := by
  have hcont : Continuous (𝓕 f : E → ℂ) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ h₁
  have hloc := hcont.locallyIntegrable (μ := volume)
  refine ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (𝓕 (h₂.toLp f))).locallyIntegrable (by norm_num)) hloc ?_
  intro g hg hs
  have hgc : ContDiff ℝ (⊤ : ℕ∞) (Complex.ofRealCLM ∘ g) :=
    Complex.ofRealCLM.contDiff.comp hg
  let s := (hs.comp_left (g := Complex.ofRealCLM) rfl).toSchwartzMap hgc
  have htest (x : E) : s x = (g x : ℂ) := rfl
  have hdist := congrArg (fun d : TemperedDistribution E ℂ => d s)
    (Lp.fourier_toTemperedDistribution_eq (h₂.toLp f))
  calc
    (∫ x, g x • (𝓕 (h₂.toLp f) : Lp ℂ 2 (volume : Measure E)) x) =
        (∫ x, (𝓕 s) x • (h₂.toLp f : E → ℂ) x) := by
      simpa only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply,
        htest, Complex.real_smul, smul_eq_mul] using hdist.symm
    _ = (∫ x, (𝓕 s) x * f x) := by
      apply integral_congr_ae
      filter_upwards [h₂.coeFn_toLp] with x hx
      rw [hx, smul_eq_mul]
    _ = ∫ x, g x • 𝓕 f x := by
      have hs₁ : Integrable (s : E → ℂ) := s.integrable
      have hswap := VectorFourier.integral_fourierIntegral_smul_eq_flip
        (L := innerₗ E) Real.continuous_fourierChar continuous_inner hs₁ h₁
      rw [flip_innerₗ] at hswap
      change (∫ x, 𝓕 (s : E → ℂ) x • f x) = ∫ x, s x • 𝓕 f x at hswap
      simpa only [SchwartzMap.fourier_coe, htest, Complex.real_smul, smul_eq_mul] using hswap

private theorem fourier_memLp_and_pairing {f g : E → ℂ}
    (hf₁ : Integrable f) (hf₂ : MemLp f 2) (hg₁ : Integrable g) (hg₂ : MemLp g 2) :
    MemLp (𝓕 f) 2 ∧ MemLp (𝓕 g) 2 ∧
      (∫ y, 𝓕 f y * (starRingEnd ℂ) (𝓕 g y)) = ∫ z, f z * (starRingEnd ℂ) (g z) := by
  have hf := ae_fourier_toLp_eq hf₁ hf₂
  have hg := ae_fourier_toLp_eq hg₁ hg₂
  refine ⟨(memLp_congr_ae hf).mp (Lp.memLp _), (memLp_congr_ae hg).mp (Lp.memLp _), ?_⟩
  calc
    (∫ y, 𝓕 f y * (starRingEnd ℂ) (𝓕 g y)) =
        inner ℂ (𝓕 (hg₂.toLp g)) (𝓕 (hf₂.toLp f)) := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hf, hg] with y hfy hgy
      simp [RCLike.inner_apply, hfy, hgy]
    _ = inner ℂ (hg₂.toLp g) (hf₂.toLp f) := Lp.inner_fourier_eq _ _
    _ = ∫ z, f z * (starRingEnd ℂ) (g z) := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hf₂.coeFn_toLp, hg₂.coeFn_toLp] with z hfz hgz
      simp [RCLike.inner_apply, hfz, hgz]

variable {m : ℕ}

/-- Fourier integral using Lebesgue coordinates and the phase `exp(i ∑ zⱼ yⱼ)`. -/
def coordinateFourierIntegral (f : (Fin m → ℝ) → ℂ) (y : Fin m → ℝ) : ℂ :=
  ∫ z : Fin m → ℝ, Complex.exp ((↑(∑ j, z j * y j) : ℂ) * Complex.I) * f z

private theorem coordinateFourierIntegral_eq_fourier
    (f : (Fin m → ℝ) → ℂ) (y : Fin m → ℝ) :
    coordinateFourierIntegral f y =
      (𝓕 (f ∘ WithLp.ofLp : EuclideanSpace ℝ (Fin m) → ℂ) :
        EuclideanSpace ℝ (Fin m) → ℂ) ((-(2 * Real.pi)⁻¹ : ℝ) •
        (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin m))) := by
  let e := MeasurableEquiv.toLp 2 (Fin m → ℝ)
  rw [coordinateFourierIntegral, Real.fourier_eq', ← (PiLp.volume_preserving_toLp (Fin m)).integral_comp
    e.measurableEmbedding]
  apply integral_congr_ae
  filter_upwards with z
  change _ = Complex.exp ((↑(-2 * Real.pi * inner ℝ (WithLp.toLp 2 z)
    ((-(2 * Real.pi)⁻¹ : ℝ) • (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin m)))) : ℂ) *
    Complex.I) * f z
  rw [real_inner_smul_right]
  have hπ : (2 * Real.pi : ℝ) ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have hcancel (u : ℝ) : -2 * Real.pi * (-(2 * Real.pi)⁻¹ * u) = u := by
    field_simp
  rw [hcancel, PiLp.inner_apply]
  congr 3
  simp [RCLike.inner_apply, mul_comm]

/-- Plancherel for the positive phase in real coordinates. The frequency dilation accounts
for the factor `(2π)^m`. -/
def CoordinatePlancherelStatement : Prop :=
  ∀ {m : ℕ} (f g : (Fin m → ℝ) → ℂ),
    Integrable f → MemLp f 2 → Integrable g → MemLp g 2 →
    MemLp (coordinateFourierIntegral f) 2 ∧ MemLp (coordinateFourierIntegral g) 2 ∧
    (∫ y, coordinateFourierIntegral f y * (starRingEnd ℂ) (coordinateFourierIntegral g y)) =
      ((2 * Real.pi : ℝ) ^ m : ℂ) * ∫ z, f z * (starRingEnd ℂ) (g z)

/-- Transfer the `L²` pairing from Euclidean space and dilate the Fourier argument. -/
theorem coordinatePlancherel : CoordinatePlancherelStatement := by
  intro m f g hf₁ hf₂ hg₁ hg₂
  let V := EuclideanSpace ℝ (Fin m)
  let e := MeasurableEquiv.toLp 2 (Fin m → ℝ)
  let F : V → ℂ := f ∘ e.symm
  let G : V → ℂ := g ∘ e.symm
  have h₁ : MeasurePreserving e := PiLp.volume_preserving_toLp (Fin m)
  have h₂ : MeasurePreserving e.symm := h₁.symm
  obtain ⟨hF, hG, hpair⟩ := fourier_memLp_and_pairing
    (f := F) (g := G)
    (h₂.integrable_comp_of_integrable hf₁) (hf₂.comp_measurePreserving h₂)
    (h₂.integrable_comp_of_integrable hg₁) (hg₂.comp_measurePreserving h₂)
  let d : ℝ := -(2 * Real.pi)⁻¹
  have hπ : 0 < (2 * Real.pi : ℝ) := mul_pos (by norm_num) Real.pi_pos
  have hd : d ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hπ.ne')
  have hscale {u : V → ℂ} (hu : MemLp u 2) :
      MemLp (fun y : V => u (d • y)) 2 := by
    have hm : Measurable (fun y : V => d • y) := (continuous_const_smul d).measurable
    refine MemLp.comp_of_map (f := fun y : V => d • y) ?_ hm.aemeasurable
    rw [Measure.map_addHaar_smul _ hd]
    exact hu.smul_measure ENNReal.ofReal_ne_top
  have hfEq : coordinateFourierIntegral f = (fun y : V => 𝓕 F (d • y)) ∘ e :=
    funext (coordinateFourierIntegral_eq_fourier f)
  have hgEq : coordinateFourierIntegral g = (fun y : V => 𝓕 G (d • y)) ∘ e :=
    funext (coordinateFourierIntegral_eq_fourier g)
  refine ⟨hfEq ▸ (hscale hF).comp_measurePreserving h₁,
    hgEq ▸ (hscale hG).comp_measurePreserving h₁, ?_⟩
  rw [hfEq, hgEq]
  change (∫ y, (fun v : V => 𝓕 F (d • v) * (starRingEnd ℂ) (𝓕 G (d • v))) (e y)) = _
  rw [h₁.integral_comp' (fun v : V => 𝓕 F (d • v) * (starRingEnd ℂ) (𝓕 G (d • v)))]
  rw [Measure.integral_comp_smul (volume : Measure V)
    (fun v => 𝓕 F v * (starRingEnd ℂ) (𝓕 G v)) d, hpair]
  have hconst : |(d ^ Module.finrank ℝ V)⁻¹| = (2 * Real.pi) ^ m := by
    have ha : |d| = (2 * Real.pi)⁻¹ := by
      rw [show d = -(2 * Real.pi)⁻¹ from rfl, abs_neg, abs_of_nonneg (inv_nonneg.mpr hπ.le)]
    rw [abs_inv, abs_pow, ha, inv_pow, inv_inv]
    simp [V]
  rw [hconst, Complex.real_smul]
  rw [← h₂.integral_comp' (fun z => f z * (starRingEnd ℂ) (g z))]
  simp only [Complex.ofReal_pow]
  rfl

end Langlands.Analysis
