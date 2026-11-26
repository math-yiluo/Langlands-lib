import Langlands.Global.RankinSelberg.ArchimedeanMellinConvolutionReflection
import Langlands.Global.RankinSelberg.RealGapMellinWeights
import Langlands.Global.RankinSelberg.RealThetaNormalizedGrowth

/-! # Normalized real gap growth from the two-scale chart reflection -/

noncomputable section

open MeasureTheory
open scoped NNReal

set_option autoImplicit false

universe u v

namespace Langlands.Global.RankinSelbergGlobal.RealGapMellinWeights

open Langlands.LocalFactor.Archimedean
open ArchimedeanMellinPair (archimedeanMellinConvolutionReflection separatedTheta theta)
open RealJacquet (HasRealPairNormalizedGrowth)
open RealThetaNormalizedGrowth (realThetaNormalizedGrowth normalizedGrowth_congr_right)
open RealWeightedKernelReflection (realWeights_data ordinaryWeight reflectedWeight
  pairReflectionFactor)

/-- The two-scale reflection with a constant phase implies normalized growth for any integrals
agreeing with the chart Mellin transforms in a right half-plane. -/
def RealGapGrowthFromSeparatedThetaStatement : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (F : X → ℂ) (Fd : Y → ℂ) (δ η : X → ℝ) (δd ηd : Y → ℝ),
    AEStronglyMeasurable F μ → AEStronglyMeasurable Fd ν →
    Measurable δ → Measurable η → Measurable δd → Measurable ηd →
    (∀ x, 0 < δ x) → (∀ x, 0 < η x) → (∀ y, 0 < δd y) → (∀ y, 0 < ηd y) →
    ∀ (σ : ℝ), (∀ z : ℝ, σ ≤ z → Integrable (fun x => ‖F x‖ * (δ x * η x) ^ z) μ) →
    (∀ z : ℝ, σ ≤ z → Integrable (fun y => ‖Fd y‖ * (δd y * ηd y) ^ z) ν) →
    ∀ (c : ℝ≥0) (hc : 0 < c) (phase : ℂ) (d dd : RealBlock) (ds es dds ees : List RealBlock)
      (b b₁ b₂ : ℝˣ) (sign sign₁ sign₂ : ℂ), sign ≠ 0 →
    (∀ s : ℂ, phase * pairReflectionFactor ds es b₁ c hc sign₁ s *
      pairReflectionFactor [d] es b₂ c hc sign₂ s = pairReflectionFactor (d :: ds) es b c hc sign s) →
    (∀ β γ : ℝ, 0 < β → 0 < γ →
      phase * separatedTheta μ F δ η
        (ordinaryWeight ds es b₁ c hc sign₁ (1 / 2) 0)
        (ordinaryWeight [d] es b₂ c hc sign₂ (1 / 2) 0) β γ =
      ((β * γ : ℝ) : ℂ) * separatedTheta ν Fd δd ηd
        (reflectedWeight dds ees (1 / 2) 0) (reflectedWeight [dd] ees (1 / 2) 0) β⁻¹ γ⁻¹) →
    ∀ (I Id : ℂ → ℂ), (∃ τ : ℝ, ∀ s : ℂ, τ < s.re →
      (∫ x, F x * ((δ x * η x : ℝ) : ℂ) ^ s ∂μ) = I s ∧
      (∫ y, Fd y * ((δd y * ηd y : ℝ) : ℂ) ^ s ∂ν) = Id s) →
    HasRealPairNormalizedGrowth (d :: ds) es (dd :: dds) ees b c hc sign I Id

set_option maxHeartbeats 900000 in
theorem realGapGrowthFromSeparatedTheta : RealGapGrowthFromSeparatedThetaStatement.{u, v} := by
  intro X Y _ _ μ ν _ _ F Fd δ η δd ηd hF hFd hδm hηm hδdm hηdm hδ hη hδd hηd
    σ hI hId c hc phase d dd ds es dds ees b b₁ b₂ sign sign₁ sign₂ hSign hE hSep I Id hRight
  let f₁ := ordinaryWeight ds es b₁ c hc sign₁ (1 / 2) 0
  let f₂ := ordinaryWeight [d] es b₂ c hc sign₂ (1 / 2) 0
  let k₁ := reflectedWeight dds ees (1 / 2) 0
  let k₂ := reflectedWeight [dd] ees (1 / 2) 0
  obtain ⟨hf₁m, hk₁m, hf₁, hk₁, _, _⟩ :=
    realWeights_data ds es dds ees b₁ c hc sign₁ (rate := 1 / 2) (by norm_num) 0
  obtain ⟨hf₂m, hk₂m, hf₂, hk₂, _, _⟩ :=
    realWeights_data [d] es [dd] ees b₂ c hc sign₂ (rate := 1 / 2) (by norm_num) 0
  have hPhase (β γ : ℝ) : separatedTheta μ F δ η (fun x => phase * f₁ x) f₂ β γ =
      phase * separatedTheta μ F δ η f₁ f₂ β γ := by
    simp only [separatedTheta, ← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun _ => by ring)
  have hSeparated (β γ : ℝ) (hβ : 0 < β) (hγ : 0 < γ) :
      separatedTheta μ F δ η (fun x => phase * f₁ x) f₂ β γ =
        ((β * γ : ℝ) : ℂ) * separatedTheta ν Fd δd ηd k₁ k₂ β⁻¹ γ⁻¹ :=
    (hPhase β γ).trans (hSep β γ hβ hγ)
  have hθ (β : ℝ) (hβ : 0 < β) :
      theta μ F (fun x => δ x * η x) (gapOrdinaryWeight c hc phase d ds es b₁ b₂ sign₁ sign₂) β =
        (β : ℂ) * theta ν Fd (fun y => δd y * ηd y) (gapReflectedWeight dd dds ees) β⁻¹ :=
    archimedeanMellinConvolutionReflection μ ν F Fd δ η δd ηd hF hFd hδm hηm hδdm hηdm hδ hη hδd
      hηd (hI σ le_rfl) (hId σ le_rfl) (fun x => phase * f₁ x) f₂ k₁ k₂
      (hf₁m.const_mul phase) hf₂m hk₁m hk₂m (ArchimedeanRealPairIdentity.rapidDecay_const_mul hf₁ phase)
      hf₂ hk₁ hk₂ hSeparated hβ
  obtain ⟨hfm, hk, hf, hkd, hfM, hkM⟩ := realGapMellinWeights c hc phase d dd ds es dds ees b b₁ b₂
    sign sign₁ sign₂ hE
  have hGrowth := realThetaNormalizedGrowth μ ν F Fd (fun x => δ x * η x) (fun y => δd y * ηd y)
    hF hFd (hδm.mul hηm) (hδdm.mul hηdm) (fun x => mul_pos (hδ x) (hη x))
    (fun y => mul_pos (hδd y) (hηd y)) σ hI hId (d :: ds) es (dd :: dds) ees b c hc _ hSign
    _ _ hfm hk hf hkd hfM hkM hθ
  exact normalizedGrowth_congr_right hGrowth hRight

end Langlands.Global.RankinSelbergGlobal.RealGapMellinWeights
