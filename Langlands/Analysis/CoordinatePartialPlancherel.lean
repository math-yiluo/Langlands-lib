import Langlands.Analysis.CoordinatePlancherel
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Plancherel in one factor of a product measure -/

noncomputable section

set_option autoImplicit false

open Filter MeasureTheory
open scoped ENNReal

namespace Langlands.Analysis

variable {m : ℕ} {Q : Type*} [MeasurableSpace Q] {μ : Measure Q}

local notation "V" => (Fin m → ℝ)

/-- The positive-phase Fourier integral in the real coordinate, leaving the other factor fixed. -/
def coordinatePartialFourier (f : V × Q → ℂ) (p : V × Q) : ℂ :=
  coordinateFourierIntegral (fun z => f (z, p.2)) p.1

variable [SFinite μ]

private theorem aestronglyMeasurable_coordinatePartialFourier {f : V × Q → ℂ}
    (hf : AEStronglyMeasurable f (volume.prod μ)) :
    AEStronglyMeasurable (coordinatePartialFourier f) (volume.prod μ) := by
  let f₀ := hf.mk f
  have hphase : Continuous (fun yz : V × V =>
      Complex.exp ((↑(∑ j, yz.2 j * yz.1 j) : ℂ) * Complex.I)) := by
    apply Complex.continuous_exp.comp
    refine (Complex.continuous_ofReal.comp ?_).mul continuous_const
    exact continuous_finsetSum _ fun j _ =>
      ((continuous_apply j).comp continuous_snd).mul ((continuous_apply j).comp continuous_fst)
  have hker : StronglyMeasurable
      (fun p : (V × Q) × V =>
        Complex.exp ((↑(∑ j, p.2 j * p.1.1 j) : ℂ) * Complex.I) * f₀ (p.2, p.1.2)) :=
    (hphase.measurable.comp (measurable_fst.fst.prodMk measurable_snd)).stronglyMeasurable.mul
      (hf.stronglyMeasurable_mk.comp_measurable (measurable_snd.prodMk measurable_fst.snd))
  refine (hker.integral_prod_right' (ν := (volume : Measure V))).aestronglyMeasurable.congr ?_
  have hswap := Measure.measurePreserving_swap (μ := μ) (ν := (volume : Measure V))
  have hslice : ∀ᵐ q ∂μ, ∀ᵐ z ∂(volume : Measure V), f (z, q) = f₀ (z, q) :=
    Measure.ae_ae_of_ae_prod (hswap.quasiMeasurePreserving.ae hf.ae_eq_mk)
  have hsnd := Measure.quasiMeasurePreserving_snd (μ := (volume : Measure V)) (ν := μ)
  filter_upwards [hsnd.ae hslice] with p hp
  apply integral_congr_ae
  filter_upwards [hp] with z hz
  exact congrArg (fun a : ℂ => Complex.exp ((↑(∑ j, z j * p.1 j) : ℂ) * Complex.I) * a) hz.symm

private theorem memLp_two_slice {f : V × Q → ℂ} (hf : MemLp f 2 (volume.prod μ)) :
    ∀ᵐ q ∂μ, MemLp (fun z => f (z, q)) 2 := by
  have hsq := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  filter_upwards [hf.aestronglyMeasurable.prodMk_right, hsq.prod_left_ae] with q hm hi
  exact (memLp_two_iff_integrable_sq_norm hm).mpr hi

private theorem integral_sq_norm_coordinateFourier {f : V → ℂ}
    (h₁ : Integrable f) (h₂ : MemLp f 2) :
    (∫ y, ‖coordinateFourierIntegral f y‖ ^ 2) =
      (2 * Real.pi) ^ m * ∫ z, ‖f z‖ ^ 2 := by
  have hp := (coordinatePlancherel f f h₁ h₂ h₁ h₂).2.2
  simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq, integral_complex_ofReal] at hp
  apply Complex.ofReal_injective
  rw [Complex.ofReal_mul, Complex.ofReal_pow]
  exact hp

private theorem memLp_coordinatePartialFourier {f : V × Q → ℂ}
    (hf : MemLp f 2 (volume.prod μ)) (h₁ : ∀ᵐ q ∂μ, Integrable (fun z => f (z, q))) :
    MemLp (coordinatePartialFourier f) 2 (volume.prod μ) := by
  have hmeas := aestronglyMeasurable_coordinatePartialFourier hf.aestronglyMeasurable
  have hin := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  refine (memLp_two_iff_integrable_sq_norm hmeas).mpr
    ((integrable_prod_iff' (hmeas.norm.pow 2)).mpr ⟨?_, ?_⟩)
  · filter_upwards [h₁, memLp_two_slice hf] with q hq₁ hq₂
    have hq := (coordinatePlancherel _ _ hq₁ hq₂ hq₁ hq₂).1
    exact (memLp_two_iff_integrable_sq_norm hq.aestronglyMeasurable).mp hq
  · refine (hin.integral_prod_right.const_mul ((2 * Real.pi) ^ m)).congr ?_
    filter_upwards [h₁, memLp_two_slice hf] with q hq₁ hq₂
    change (2 * Real.pi) ^ m * (∫ z, ‖f (z, q)‖ ^ 2) =
      ∫ y, ‖‖coordinatePartialFourier f (y, q)‖ ^ 2‖
    simpa only [Real.norm_of_nonneg (sq_nonneg _), coordinatePartialFourier] using
      (integral_sq_norm_coordinateFourier hq₁ hq₂).symm

/-- Partial Plancherel for square-integrable functions with almost everywhere integrable
frequency slices. Both the frequency and the Fourier variable carry Lebesgue measure. -/
def CoordinatePartialPlancherelStatement : Prop :=
  ∀ {m : ℕ} {Q : Type*} [MeasurableSpace Q] (μ : Measure Q) [SFinite μ]
    (f g : (Fin m → ℝ) × Q → ℂ),
    MemLp f 2 (volume.prod μ) → MemLp g 2 (volume.prod μ) →
    (∀ᵐ q ∂μ, Integrable (fun z => f (z, q))) →
    (∀ᵐ q ∂μ, Integrable (fun z => g (z, q))) →
    MemLp (coordinatePartialFourier f) 2 (volume.prod μ) ∧
    MemLp (coordinatePartialFourier g) 2 (volume.prod μ) ∧
    (∫ p, coordinatePartialFourier f p * (starRingEnd ℂ) (coordinatePartialFourier g p)
      ∂(volume.prod μ)) =
      ((2 * Real.pi : ℝ) ^ m : ℂ) * ∫ p, f p * (starRingEnd ℂ) (g p) ∂(volume.prod μ)

/-- Apply scalar Plancherel on almost every slice and use Fubini on both pairings. -/
theorem coordinatePartialPlancherel : CoordinatePartialPlancherelStatement := by
  intro m Q _ μ _ f g hf hg hf₁ hg₁
  have hF := memLp_coordinatePartialFourier hf hf₁
  have hG := memLp_coordinatePartialFourier hg hg₁
  have hpair : Integrable (fun p => f p * (starRingEnd ℂ) (g p)) (volume.prod μ) :=
    hf.integrable_mul hg.star
  have hpairFourier : Integrable
      (fun p => coordinatePartialFourier f p * (starRingEnd ℂ) (coordinatePartialFourier g p))
      (volume.prod μ) := hF.integrable_mul hG.star
  refine ⟨hF, hG, ?_⟩
  rw [integral_prod_symm _ hpairFourier, integral_prod_symm _ hpair, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hf₁, hg₁, memLp_two_slice hf, memLp_two_slice hg] with q hqf hqg hqf₂ hqg₂
  exact (coordinatePlancherel _ _ hqf hqf₂ hqg hqg₂).2.2

end Langlands.Analysis
