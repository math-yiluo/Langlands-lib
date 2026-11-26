import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Pushforward of an integrable function along a measurable map -/

noncomputable section

namespace Langlands.HarmonicAnalysis

open MeasureTheory Set Function
open scoped ENNReal

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [SigmaFinite ν] {p : X → Y}

private theorem exists_pushforward_nonneg (hp : Measurable p) (hμν : μ.map p ≪ ν)
    {f : X → ℝ} (hf : Integrable f μ) (hf₀ : ∀ x, 0 ≤ f x) :
    ∃ r : Y → ℝ, Integrable r ν ∧ ∀ g : Y → ℂ, Measurable g →
      (∫ y, r y • g y ∂ν) = ∫ x, f x • g (p x) ∂μ := by
  let ξ := μ.withDensity (fun x => ENNReal.ofReal (f x))
  have : IsFiniteMeasure ξ := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
    exact ((lintegral_ofReal_ne_top_iff_integrable hf.aestronglyMeasurable
      (Filter.Eventually.of_forall hf₀)).2 hf).lt_top
  let η := ξ.map p
  have hη : η ≪ ν := Measure.AbsolutelyContinuous.mk fun B hB hν => by
    rw [Measure.map_apply hp hB]
    exact withDensity_absolutelyContinuous μ _ (by
      rw [← Measure.map_apply hp hB]
      exact hμν hν)
  let r := fun y => (η.rnDeriv ν y).toReal
  refine ⟨r, Measure.integrable_toReal_rnDeriv, fun g hg => ?_⟩
  calc
    (∫ y, r y • g y ∂ν) = ∫ y, g y ∂(ν.withDensity (η.rnDeriv ν)) :=
      (integral_withDensity_eq_integral_toReal_smul (Measure.measurable_rnDeriv _ _)
        (Measure.rnDeriv_lt_top _ _) _).symm
    _ = ∫ x, g (p x) ∂ξ := by
      rw [Measure.withDensity_rnDeriv_eq _ _ hη]
      exact integral_map hp.aemeasurable hg.aestronglyMeasurable
    _ = ∫ x, f x • g (p x) ∂μ := by
      rw [integral_withDensity_eq_integral_toReal_smul₀ hf.aemeasurable.ennreal_ofReal
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _]
      simp_rw [ENNReal.toReal_ofReal (hf₀ _)]

private theorem exists_pushforward_real (hp : Measurable p) (hμν : μ.map p ≪ ν)
    {f : X → ℝ} (hf : Integrable f μ) :
    ∃ r : Y → ℝ, Integrable r ν ∧ ∀ (g : Y → ℂ), Measurable g →
      (∃ C : ℝ, ∀ y, ‖g y‖ ≤ C) →
      (∫ y, r y • g y ∂ν) = ∫ x, f x • g (p x) ∂μ := by
  obtain ⟨r, hr, hR⟩ := exists_pushforward_nonneg hp hμν hf.pos_part (fun _ => le_max_right _ _)
  obtain ⟨s, hs, hS⟩ := exists_pushforward_nonneg hp hμν hf.neg_part (fun _ => le_max_right _ _)
  refine ⟨fun y => r y - s y, hr.sub hs, ?_⟩
  rintro g hg ⟨C, hC⟩
  have hsplit (a : ℝ) : max a 0 - max (-a) 0 = a := by
    rcases le_total 0 a with h | h
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), sub_zero]
    · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h), zero_sub, neg_neg]
  rw [show (fun y => (r y - s y) • g y) = fun y => r y • g y - s y • g y by
    funext y; exact sub_smul _ _ _]
  have hr' : Integrable (fun y => r y • g y) ν :=
    hr.smul_bdd C hg.aestronglyMeasurable (Filter.Eventually.of_forall hC)
  have hs' : Integrable (fun y => s y • g y) ν :=
    hs.smul_bdd C hg.aestronglyMeasurable (Filter.Eventually.of_forall hC)
  have hpos : Integrable (fun x => max (f x) 0 • g (p x)) μ :=
    hf.pos_part.smul_bdd C (hg.comp hp).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => hC (p x))
  have hneg : Integrable (fun x => max (-f x) 0 • g (p x)) μ :=
    hf.neg_part.smul_bdd C (hg.comp hp).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => hC (p x))
  rw [integral_sub hr' hs', hR g hg, hS g hg, ← integral_sub hpos hneg]
  simp_rw [← sub_smul, hsplit]

/-- An integrable complex weight has an integrable pushforward density if the pushforward
of the underlying measure is absolutely continuous with respect to the σ-finite target measure. -/
def IntegrablePushforwardStatement (μ : Measure X) (ν : Measure Y) [SigmaFinite ν]
    (p : X → Y) : Prop :=
  Measurable p → μ.map p ≪ ν → ∀ f : X → ℂ, Integrable f μ →
    ∃ r : Y → ℂ, Integrable r ν ∧ ∀ (g : Y → ℂ), Measurable g →
      (∃ C : ℝ, ∀ y, ‖g y‖ ≤ C) →
      (∫ y, r y * g y ∂ν) = ∫ x, f x * g (p x) ∂μ

/-- Use Radon–Nikodym for the four positive measures from the real and imaginary parts. -/
theorem integrablePushforward : IntegrablePushforwardStatement μ ν p := by
  intro hp hμν f hf
  obtain ⟨r, hr, hR⟩ := exists_pushforward_real hp hμν hf.re
  obtain ⟨s, hs, hS⟩ := exists_pushforward_real hp hμν hf.im
  let r' := fun y => ((r y : ℝ) : ℂ)
  let s' := fun y => ((s y : ℝ) : ℂ)
  have hr' : Integrable r' ν := Complex.ofRealCLM.integrable_comp hr
  have hs' : Integrable s' ν := Complex.ofRealCLM.integrable_comp hs
  refine ⟨fun y => r' y + Complex.I * s' y, hr'.add (hs'.const_mul _), ?_⟩
  rintro g hg ⟨C, hC⟩
  have hg' := (hg.comp hp).aestronglyMeasurable (μ := μ)
  have hC' := Filter.Eventually.of_forall (fun x => hC (p x)) (f := ae μ)
  have hrmul := hr'.mul_bdd hg.aestronglyMeasurable (Filter.Eventually.of_forall hC)
  have hsmul := hs'.mul_bdd hg.aestronglyMeasurable (Filter.Eventually.of_forall hC)
  have hfremul : Integrable (fun x => (f x).re * g (p x)) μ :=
    (Complex.ofRealCLM.integrable_comp hf.re).mul_bdd hg' hC'
  have hfimmul : Integrable (fun x => (f x).im * g (p x)) μ :=
    (Complex.ofRealCLM.integrable_comp hf.im).mul_bdd hg' hC'
  have hRe := hR g hg ⟨C, hC⟩
  have hIm := hS g hg ⟨C, hC⟩
  simp only [Complex.real_smul] at hRe hIm
  calc
    (∫ y, (r' y + Complex.I * s' y) * g y ∂ν) =
        (∫ y, r' y * g y ∂ν) + Complex.I * ∫ y, s' y * g y ∂ν := by
      simp_rw [add_mul, mul_assoc]
      rw [integral_add hrmul (hsmul.const_mul _), integral_const_mul]
    _ = (∫ x, (f x).re * g (p x) ∂μ) + Complex.I * ∫ x, (f x).im * g (p x) ∂μ := by
      rw [show (∫ y, r' y * g y ∂ν) = ∫ x, (f x).re * g (p x) ∂μ from hRe,
        show (∫ y, s' y * g y ∂ν) = ∫ x, (f x).im * g (p x) ∂μ from hIm]
    _ = ∫ x, f x * g (p x) ∂μ := by
      have hI : Integrable (fun x => Complex.I * ((f x).im * g (p x))) μ :=
        hfimmul.const_mul _
      rw [← integral_const_mul, ← integral_add hfremul hI]
      simp_rw [← mul_assoc Complex.I, ← add_mul, mul_comm Complex.I, Complex.re_add_im]

end Langlands.HarmonicAnalysis
