import Langlands.Global.RankinSelberg.ArchimedeanIntegrals
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! # The real-place Fourier transform of a Schwartz function is a Schwartz function -/

noncomputable section

open MeasureTheory
open scoped NNReal SchwartzMap FourierTransform Real InnerProductSpace

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealFourierSchwartz

open ArchimedeanLocal

variable {n : ℕ}

/-- The product of the self-dual measures on `ℝⁿ` is a constant multiple of Lebesgue measure
(uniqueness of additive Haar measure). -/
theorem exists_pi_eq_smul_volume (b : ℝˣ) :
    ∃ c : ℝ≥0, Measure.pi (fun _ : Fin n => (realSelfDualMeasure b).measure) =
      c • (volume : Measure (Fin n → ℝ)) :=
  ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩

/-- The identification of Euclidean space with `Fin n → ℝ`. -/
abbrev euclidEquiv (n : ℕ) : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)

/-- The linear change of variables `x ↦ -b x` from `Fin n → ℝ` to Euclidean space. -/
def scaleEquiv (n : ℕ) (b : ℝˣ) : (Fin n → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (euclidEquiv n).symm.trans (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (-b))

theorem scaleEquiv_apply (b : ℝˣ) (x : Fin n → ℝ) (j : Fin n) :
    scaleEquiv n b x j = -((b : ℝ) * x j) := by
  simp [scaleEquiv, Units.smul_def]

/-- `realFourierTransform b Φ (x) = c · 𝓕(Φ ∘ e)(-b x)` with Mathlib's Fourier transform on
Euclidean space. -/
theorem realFourierTransform_eq (b : ℝˣ) (Φ : (Fin n → ℝ) → ℂ) (c : ℝ≥0)
    (hc : Measure.pi (fun _ : Fin n => (realSelfDualMeasure b).measure) =
      c • (volume : Measure (Fin n → ℝ)))
    (x : Fin n → ℝ) :
    realFourierTransform b Φ x =
      ((c : ℝ) : ℂ) * 𝓕 (Φ ∘ euclidEquiv n) (scaleEquiv n b x) := by
  rw [realFourierTransform, ArchimedeanLocal.fourierTransform, hc, integral_smul_nnreal_measure,
    NNReal.smul_def, Complex.real_smul]
  congr 1
  rw [Real.fourier_eq]
  refine ((EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n)).integral_comp'
    (fun y => Φ y * (LocalFactor.Archimedean.realScaledCharacter b).complex
      (∑ j, y j * x j))).symm.trans ?_
  congr 1
  funext v
  rw [Circle.smul_def, smul_eq_mul, mul_comm]
  congr 1
  simp only [Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply,
    LocalFactor.Archimedean.realScaledCharacter_apply, Real.fourierChar_apply]
  congr 3
  rw [PiLp.inner_apply]
  simp only [scaleEquiv_apply, RCLike.inner_apply, conj_trivial, MeasurableEquiv.coe_toLp_symm,
    neg_mul, Finset.sum_neg_distrib, neg_neg, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **The real Fourier transform preserves Schwartz functions.** -/
theorem exists_schwartz_eq (b : ℝˣ) (Φ : 𝓢(Fin n → ℝ, ℂ)) :
    ∃ Ψ : 𝓢(Fin n → ℝ, ℂ), ⇑Ψ = realFourierTransform b Φ := by
  obtain ⟨c, hc⟩ := exists_pi_eq_smul_volume (n := n) b
  let ΦV : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (euclidEquiv n) Φ
  refine ⟨((c : ℝ) : ℂ) • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (scaleEquiv n b) (𝓕 ΦV),
    ?_⟩
  funext x
  rw [realFourierTransform_eq b Φ c hc x, smul_apply, smul_eq_mul,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, SchwartzMap.fourier_coe]
  rfl

end Langlands.Global.RankinSelbergGlobal.RealFourierSchwartz
