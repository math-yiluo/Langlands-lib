import Langlands.Global.RankinSelberg.ArchimedeanMellinConvolutionReflection
import Langlands.Global.RankinSelberg.ComplexGapMellinWeights
import Langlands.Global.RankinSelberg.ComplexThetaNormalizedGrowth

/-! # Normalized complex gap growth from the two-scale chart reflection -/

noncomputable section

open MeasureTheory

set_option autoImplicit false

universe u v

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapMellinWeights

open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open ArchimedeanMellinPair (archimedeanMellinConvolutionReflection separatedTheta theta)
open ComplexJacquet (HasComplexPairNormalizedGrowth complexCentralSign_sq)
open ComplexThetaNormalizedGrowth (complexThetaNormalizedGrowth normalizedGrowth_congr_right)
open ComplexWeightedKernelReflection (complexWeights_data ordinaryWeight reflectedWeight)

/-- The two-scale reflection with the adjoining phase implies normalized growth for
any integrals agreeing with the chart Mellin transforms in a right half-plane. -/
def ComplexGapGrowthFromSeparatedThetaStatement : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (F : X → ℂ) (Fd : Y → ℂ) (δ η : X → ℝ) (δd ηd : Y → ℝ),
    AEStronglyMeasurable F μ → AEStronglyMeasurable Fd ν →
    Measurable δ → Measurable η → Measurable δd → Measurable ηd →
    (∀ x, 0 < δ x) → (∀ x, 0 < η x) → (∀ y, 0 < δd y) → (∀ y, 0 < ηd y) →
    ∀ (σ : ℝ), (∀ z : ℝ, σ ≤ z → Integrable (fun x => ‖F x‖ * (δ x * η x) ^ z) μ) →
    (∀ z : ℝ, σ ≤ z → Integrable (fun y => ‖Fd y‖ * (δd y * ηd y) ^ z) ν) →
    ∀ (r : ℕ) (d : ComplexCharacterData) (ds es : List ComplexCharacterData) (a : ℂˣ),
    (∀ b c : ℝ, 0 < b → 0 < c →
      adjoiningPhase d es * separatedTheta μ F δ η
        (ordinaryWeight ds es (-a) (complexCentralSign es ^ r) (1 / 2) 0)
        (ordinaryWeight [d] es a 1 (1 / 2) 0) b c =
      ((b * c : ℝ) : ℂ) * separatedTheta ν Fd δd ηd
        (reflectedWeight ds es (1 / 2) 0) (reflectedWeight [d] es (1 / 2) 0) b⁻¹ c⁻¹) →
    ∀ (I Id : ℂ → ℂ), (∃ τ : ℝ, ∀ s : ℂ, τ < s.re →
      (∫ x, F x * ((δ x * η x : ℝ) : ℂ) ^ s ∂μ) = I s ∧
      (∫ y, Fd y * ((δd y * ηd y : ℝ) : ℂ) ^ s ∂ν) = Id s) →
    HasComplexPairNormalizedGrowth (d :: ds) es (-a) (complexCentralSign es ^ (r + 1)) I Id

set_option maxHeartbeats 900000 in
theorem complexGapGrowthFromSeparatedTheta : ComplexGapGrowthFromSeparatedThetaStatement.{u, v} := by
  intro X Y _ _ μ ν _ _ F Fd δ η δd ηd hF hFd hδm hηm hδdm hηdm hδ hη hδd hηd
    σ hI hId r d ds es a hSep I Id hRight
  let f₁ := ordinaryWeight ds es (-a) (complexCentralSign es ^ r) (1 / 2) 0
  let f₂ := ordinaryWeight [d] es a 1 (1 / 2) 0
  let k₁ := reflectedWeight ds es (1 / 2) 0
  let k₂ := reflectedWeight [d] es (1 / 2) 0
  let c₀ := adjoiningPhase d es
  obtain ⟨hf₁m, hk₁m, hf₁, hk₁, _, _⟩ :=
    complexWeights_data ds es (-a) (complexCentralSign es ^ r) (rate := 1 / 2) (by norm_num) 0
  obtain ⟨hf₂m, hk₂m, hf₂, hk₂, _, _⟩ := complexWeights_data [d] es a 1 (rate := 1 / 2) (by norm_num) 0
  have hPhase (b c : ℝ) : separatedTheta μ F δ η (fun x => c₀ * f₁ x) f₂ b c =
      c₀ * separatedTheta μ F δ η f₁ f₂ b c := by
    simp only [separatedTheta, ← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun _ => by ring)
  have hSeparated (b c : ℝ) (hb : 0 < b) (hc : 0 < c) :
      separatedTheta μ F δ η (fun x => c₀ * f₁ x) f₂ b c =
        ((b * c : ℝ) : ℂ) * separatedTheta ν Fd δd ηd k₁ k₂ b⁻¹ c⁻¹ :=
    (hPhase b c).trans (hSep b c hb hc)
  have hθ (b : ℝ) (hb : 0 < b) :
      theta μ F (fun x => δ x * η x) (gapOrdinaryWeight r d ds es a) b =
        (b : ℂ) * theta ν Fd (fun y => δd y * ηd y) (gapReflectedWeight d ds es) b⁻¹ :=
    archimedeanMellinConvolutionReflection μ ν F Fd δ η δd ηd hF hFd hδm hηm hδdm hηdm hδ hη hδd hηd
      (hI σ le_rfl) (hId σ le_rfl) (fun x => c₀ * f₁ x) f₂ k₁ k₂
      (hf₁m.const_mul c₀) hf₂m hk₁m hk₂m (ArchimedeanRealPairIdentity.rapidDecay_const_mul hf₁ c₀)
      hf₂ hk₁ hk₂ hSeparated hb
  have hSign : complexCentralSign es ^ (r + 1) ≠ 0 := pow_ne_zero _ (by
    intro hZero
    have hSign := complexCentralSign_sq es
    simp [hZero] at hSign)
  obtain ⟨hfm, hk, hf, hkd, hfM, hkM⟩ := complexGapMellinWeights r d ds es a
  have hGrowth := complexThetaNormalizedGrowth μ ν F Fd (fun x => δ x * η x) (fun y => δd y * ηd y)
    hF hFd (hδm.mul hηm) (hδdm.mul hηdm) (fun x => mul_pos (hδ x) (hη x))
    (fun y => mul_pos (hδd y) (hηd y)) σ hI hId (d :: ds) es (-a) _ hSign
    _ _ hfm hk hf hkd hfM hkM hθ
  exact normalizedGrowth_congr_right hGrowth hRight

end Langlands.Global.RankinSelbergGlobal.ComplexGapMellinWeights
