import Langlands.Global.RankinSelberg.RealGodementRowFourierInversion
import Langlands.Representation.Archimedean.SmoothAction
import Langlands.Representation.Archimedean.SmoothCompactOrbitIntegral
import Langlands.Representation.Archimedean.SmoothModerateGrowth

/-! # Schwartz row absorption from a real additive covariance law -/

noncomputable section

open MeasureTheory
open scoped ContDiff Manifold SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealSmoothRowCharacterAbsorption

open Langlands.Archimedean Langlands.Archimedean.DerivativeSmoothVectors Langlands.HarmonicAnalysis
open Langlands.LocalFactor.Archimedean
open ArchimedeanLocal

universe uA uE uG

section Orbit

variable {A : Type uA} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [FiniteDimensional ℝ A] {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (R : Aˣ →* (E →L[ℂ] E))

local notation "I" => 𝓘(ℝ, A)
local notation "D" => DerivativeSmoothVectors I R

private theorem integrable_columnOrbitWord (hR : IsContinuousRepresentation R)
    {n : ℕ} (μ : Measure (Fin n → ℝ)) [μ.IsAddHaarMeasure]
    (j : (Fin n → ℝ) → Aˣ) (hj : Continuous j) {K C : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (d : ℕ)
    (hHeight : ∀ x, unitHeight (j x) ≤ K * max 1 ‖x‖)
    (hNorm : ∀ x, ‖R (j x)‖ ≤ C * unitHeight (j x) ^ d)
    (F : 𝓢((Fin n → ℝ), ℂ)) (v : D) (s : List A) :
    Integrable (fun x => derivativeCLM I R s (F x • representation I R (j x) v)) μ := by
  let b := Module.finBasis ℝ A
  let k := d + 2 * s.length
  let q := C * (s.map fun X => ‖X‖).prod * wordOrderSeminorm R b s.length v
  have hq : 0 ≤ q := mul_nonneg (mul_nonneg hC (List.prod_nonneg (by simp))) (apply_nonneg _ _)
  have hcont : Continuous (fun x => representation I R (j x) v) :=
    (continuous_representation_units R hR).comp (hj.prodMk continuous_const)
  have hB := ((F.integrable (μ := μ)).norm.add (F.integrable_pow_mul μ k)).const_mul (K ^ k * q)
  refine hB.mono' ((derivativeCLM I R s).continuous.comp (F.continuous.smul hcont)).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  rw [map_smul, norm_smul]
  change ‖F x‖ * wordSeminormFamily I R s (representation I R (j x) v) ≤
    (K ^ k * q) * (‖F x‖ + ‖x‖ ^ k * ‖F x‖)
  have hmax : (max 1 ‖x‖) ^ k ≤ 1 + ‖x‖ ^ k := by
    rcases le_total (1 : ℝ) ‖x‖ with h | h
    · rw [max_eq_right h]
      exact le_add_of_nonneg_left zero_le_one
    · rw [max_eq_left h, one_pow]
      exact le_add_of_nonneg_right (by positivity)
  have hheight : unitHeight (j x) ^ k ≤ K ^ k * (1 + ‖x‖ ^ k) := by
    calc
      _ ≤ (K * max 1 ‖x‖) ^ k := pow_le_pow_left₀ (zero_le_one.trans (one_le_unitHeight _))
        (hHeight x) k
      _ ≤ _ := by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_left hmax (pow_nonneg hK _)
  calc
    _ ≤ ‖F x‖ * (unitHeight (j x) ^ k * q) :=
      mul_le_mul_of_nonneg_left (wordSeminormFamily_representation_le R b s (j x) v hC (hNorm x))
        (norm_nonneg _)
    _ ≤ ‖F x‖ * ((K ^ k * (1 + ‖x‖ ^ k)) * q) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hheight hq) (norm_nonneg _)
    _ = _ := by ring

end Orbit

/-- A single averaged vector realizes the Schwartz multiplier simultaneously for all evaluations
with the supplied column covariance. -/
def RealSmoothRowCharacterAbsorptionAllEvaluationsStatement : Prop :=
  ∀ {A : Type uA} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (R : Aˣ →* (E →L[ℂ] E)),
    let D := DerivativeSmoothVectors 𝓘(ℝ, A) R
    IsContinuousRepresentation R → ∀ (n : ℕ) (a : ℝˣ) (j : (Fin n → ℝ) → Aˣ),
      Continuous j →
      (∃ K : ℝ, 0 ≤ K ∧ ∀ x, unitHeight (j x) ≤ K * max 1 ‖x‖) →
      (∃ (C : ℝ) (d : ℕ), 0 ≤ C ∧ ∀ x, ‖R (j x)‖ ≤ C * unitHeight (j x) ^ d) →
      ∀ (G : Type uG) (L : G → D →L[ℂ] ℂ) (p : G → Aˣ) (row : G → Fin n → ℝ),
        (∀ g x v, L g (representation 𝓘(ℝ, A) R (p g) (representation 𝓘(ℝ, A) R (j x) v)) =
          (realScaledCharacter a).complex (∑ i, x i * row g i) * L g (representation 𝓘(ℝ, A) R (p g) v)) →
        ∀ (v : D) (Φ : 𝓢((Fin n → ℝ), ℂ)), ∃ w : D, ∀ g : G,
          L g (representation 𝓘(ℝ, A) R (p g) w) = L g (representation 𝓘(ℝ, A) R (p g) v) * Φ (row g)

set_option maxHeartbeats 600000 in
theorem realSmoothRowCharacterAbsorptionAllEvaluations : RealSmoothRowCharacterAbsorptionAllEvaluationsStatement.{uA, uE, uG} := by
  intro A _ _ _ _ E _ _ _ R D hR n a j hj hH hN G L p row hCov v Φ
  obtain ⟨K, hK, hHeight⟩ := hH
  obtain ⟨C, d, hC, hNorm⟩ := hN
  let F := RealGodement.realRowSchwartzFourier n (-a) Φ
  let μ := rowMeasure (realSelfDualMeasure a) n
  let : (realSelfDualMeasure a).measure.IsAddHaarMeasure := (realSelfDualMeasure a).isAddHaar
  let : SigmaFinite (realSelfDualMeasure a).measure := inferInstance
  let : μ.IsAddHaarMeasure := rowMeasure_isAddHaar _ _
  obtain ⟨w, _, hw⟩ := smoothWordIntegral R μ hR (fun x => F x • representation 𝓘(ℝ, A) R (j x) v)
    (integrable_columnOrbitWord R hR μ j hj hK hC d hHeight hNorm F v)
  refine ⟨w, fun g => ?_⟩
  let W := L g (representation 𝓘(ℝ, A) R (p g) v)
  let Lg := (L g).comp (SmoothAction.derivativeAction 𝓘(ℝ, A) R (p g))
  have hpt (x : Fin n → ℝ) : Lg (F x • representation 𝓘(ℝ, A) R (j x) v) =
      (F x * (realScaledCharacter a).complex (∑ i, x i * row g i)) * W := by
    rw [map_smul, smul_eq_mul]
    change F x * L g (representation 𝓘(ℝ, A) R (p g) (representation 𝓘(ℝ, A) R (j x) v)) = _
    rw [hCov, mul_assoc]
  change Lg w = W * Φ (row g)
  calc
    Lg w = ∫ x, Lg (F x • representation 𝓘(ℝ, A) R (j x) v) ∂μ := (hw Lg).2
    _ = ∫ x, (F x * (realScaledCharacter a).complex (∑ i, x i * row g i)) * W ∂μ :=
      integral_congr_ae (ae_of_all _ hpt)
    _ = W * realFourierTransform a F (row g) := by
      rw [integral_mul_const]
      exact mul_comm _ W
    _ = W * Φ (row g) := by
      rw [← RealGodement.realRowSchwartzFourier_apply,
        show RealGodement.realRowSchwartzFourier n a F = Φ by
          simpa only [neg_neg, F] using RealGodement.realRowSchwartzFourier_neg_comp n (-a) Φ]

/-- A polynomially bounded column action with additive row covariance realizes arbitrary Schwartz
multiplication of that row by a vector in the genuine ambient smooth carrier. -/
def RealSmoothRowCharacterAbsorptionStatement : Prop :=
  ∀ {A : Type uA} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (R : Aˣ →* (E →L[ℂ] E)),
    let D := DerivativeSmoothVectors 𝓘(ℝ, A) R
    IsContinuousRepresentation R → ∀ (n : ℕ) (a : ℝˣ) (j : (Fin n → ℝ) → Aˣ),
      Continuous j →
      (∃ K : ℝ, 0 ≤ K ∧ ∀ x, unitHeight (j x) ≤ K * max 1 ‖x‖) →
      (∃ (C : ℝ) (d : ℕ), 0 ≤ C ∧ ∀ x, ‖R (j x)‖ ≤ C * unitHeight (j x) ^ d) →
      ∀ (L : D →L[ℂ] ℂ) {G : Type uG} (p : G → Aˣ) (row : G → Fin n → ℝ),
        (∀ g x v, L (representation 𝓘(ℝ, A) R (p g) (representation 𝓘(ℝ, A) R (j x) v)) =
          (realScaledCharacter a).complex (∑ i, x i * row g i) * L (representation 𝓘(ℝ, A) R (p g) v)) →
        ∀ (v : D) (Φ : 𝓢((Fin n → ℝ), ℂ)), ∃ w : D, ∀ g : G,
          L (representation 𝓘(ℝ, A) R (p g) w) = L (representation 𝓘(ℝ, A) R (p g) v) * Φ (row g)

theorem realSmoothRowCharacterAbsorption : RealSmoothRowCharacterAbsorptionStatement.{uA, uE, uG} := by
  intro A _ _ _ _ E _ _ _ R D hR n a j hj hH hN L G p row hCov v Φ
  exact realSmoothRowCharacterAbsorptionAllEvaluations R hR n a j hj hH hN G (fun _ => L) p row hCov v Φ

end Langlands.Global.RankinSelbergGlobal.RealSmoothRowCharacterAbsorption
