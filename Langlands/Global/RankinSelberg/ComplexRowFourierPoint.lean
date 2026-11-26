import Langlands.LocalFactor.ArchimedeanScaling
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.RingTheory.Complex

/-! # Pointwise Fourier vanishing on complex rows -/

noncomputable section

open MeasureTheory Filter
open scoped Topology FourierTransform RealInnerProductSpace

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.ComplexRowFourier

open Langlands.LocalFactor.Archimedean

variable {m : ℕ}

private abbrev E (m : ℕ) := EuclideanSpace ℂ (Fin m)

private def rowEquiv (m : ℕ) : E m ≃L[ℝ] (Fin m → ℂ) :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℂ)

private theorem rowEquiv_apply (v : E m) : rowEquiv m v = WithLp.ofLp v := rfl

private theorem exists_map_volume :
    ∃ c : NNReal, c ≠ 0 ∧ (volume : Measure (E m)).map (rowEquiv m) = c • volume := by
  have : ((volume : Measure (E m)).map (rowEquiv m)).IsAddHaarMeasure :=
    (rowEquiv m).isAddHaarMeasure_map volume
  exact ⟨_, (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne',
    Measure.isAddLeftInvariant_eq_smul _ _⟩

private theorem trace_phase (a : ℂˣ) (η w : Fin m → ℂ) :
    Algebra.trace ℝ ℂ ((a : ℂ) * ∑ i, η i * (-(star (w i)) / (2 * (a : ℂ)))) =
      -(∑ i, (star (η i) * w i).re) := by
  have hmul : (a : ℂ) * ∑ i, η i * (-(star (w i)) / (2 * (a : ℂ))) =
      ∑ i, (-(η i * star (w i)) / 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp [a.ne_zero]
  rw [hmul, map_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.trace_complex_apply]
  simp only [Complex.div_ofNat_re, Complex.neg_re, Complex.mul_re, Complex.star_def,
    Complex.conj_re, Complex.conj_im]
  ring

private theorem real_inner_apply (v w : E m) :
    ⟪v, w⟫ = ∑ i, (star (WithLp.ofLp v i) * WithLp.ofLp w i).re := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.inner, Complex.star_def, mul_comm]

/-- An integrable function of complex rows that is continuous at one point vanishes there
when its integrals against all characters `η ↦ ψ_a(∑ᵢ ηᵢ xᵢ)` vanish. -/
theorem eq_zero_of_character_integrals (a : ℂˣ) {Ψ : (Fin m → ℂ) → ℂ}
    (hΨ : Integrable Ψ) {η₀ : Fin m → ℂ} (hc : ContinuousAt Ψ η₀)
    (hzero : ∀ x : Fin m → ℂ,
      ∫ η, (complexScaledCharacter a).complex (∑ i, η i * x i) * Ψ η = 0) :
    Ψ η₀ = 0 := by
  let e := rowEquiv m
  obtain ⟨c, hc0, hmap⟩ := exists_map_volume (m := m)
  let f : E m → ℂ := fun v => Ψ (e v)
  have he : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have hf : Integrable f := by
    have h₁ : Integrable Ψ ((volume : Measure (E m)).map e) := by
      rw [hmap]
      exact hΨ.smul_measure_nnreal
    exact (he.integrable_map_iff.mp h₁)
  have hFourier : 𝓕 f = 0 := by
    funext w
    rw [Real.fourier_eq, Pi.zero_apply]
    have hchar (v : E m) : 𝐞 (-⟪v, w⟫) • f v =
        (complexScaledCharacter a).complex
          (∑ i, e v i * (-(star (WithLp.ofLp w i)) / (2 * (a : ℂ)))) * Ψ (e v) := by
      rw [Circle.smul_def]
      change (Real.fourierChar (-⟪v, w⟫) : ℂ) * f v = (complexScaledCharacter a _ : ℂ) * _
      rw [complexScaledCharacter_apply, trace_phase, real_inner_apply]
      rfl
    simp_rw [hchar]
    have hint := he.integral_map (μ := volume)
      (fun η => (complexScaledCharacter a).complex
        (∑ i, η i * (-(star (WithLp.ofLp w i)) / (2 * (a : ℂ)))) * Ψ η)
    rw [← hint, hmap, integral_smul_nnreal_measure, hzero, smul_zero]
  have hcont : ContinuousAt f (e.symm η₀) := by
    have hc' : ContinuousAt Ψ (e (e.symm η₀)) := by simpa using hc
    exact hc'.comp e.continuous.continuousAt
  have hinv := hf.fourierInv_fourier_eq (by rw [hFourier]; exact integrable_zero _ _ _) hcont
  rw [hFourier] at hinv
  have h0 : 𝓕⁻ (0 : E m → ℂ) (e.symm η₀) = 0 := by
    rw [Real.fourierInv_eq]
    simp
  simpa [f, h0] using hinv.symm

end Langlands.Global.RankinSelbergGlobal.ComplexRowFourier
