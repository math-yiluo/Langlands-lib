import Langlands.Global.RankinSelberg.ComplexWeightedKernelReflection
import Langlands.Global.RankinSelberg.ArchimedeanGaussianMellinPair
import Langlands.Global.RankinSelberg.ArchimedeanRealPairFactor
import Langlands.Global.RankinSelberg.RealLocalNormalizedGrowth

/-! # Weighted reflection for the real pair factors -/

noncomputable section

open MeasureTheory Complex Set
open scoped NNReal

set_option autoImplicit false

universe u v

namespace Langlands.Global.RankinSelbergGlobal.RealWeightedKernelReflection

open Langlands.LocalFactor.Archimedean
open ArchimedeanMellinPair (RapidDecay theta)
open ArchimedeanRealPairIdentity (norm_kernel kernel_zero_eq)
open ArchimedeanInverseMellin
open ArchimedeanRealPairFactor (realLFactor_stripExpType realEpsilon_stripExpType realEpsilon_differentiable)
open RealJacquet (HasRealPairNormalizedGrowth)

/-- The reflection factor including the constant central sign. -/
def pairReflectionFactor (ds es : List RealBlock) (b : ℝˣ) (c : ℝ≥0) (hc : 0 < c) (sign : ℂ)
    (s : ℂ) : ℂ :=
  sign * (realPairEpsilon ds es b c hc s : ℂ)

theorem differentiable_pairReflectionFactor (ds es : List RealBlock) (b : ℝˣ) (c : ℝ≥0)
    (hc : 0 < c) (sign : ℂ) : Differentiable ℂ (pairReflectionFactor ds es b c hc sign) :=
  (realEpsilon_differentiable (realPairBlocks ds es) b c hc).const_mul sign

theorem stripExpType_pairReflectionFactor (ds es : List RealBlock) (b : ℝˣ) (c : ℝ≥0)
    (hc : 0 < c) (sign : ℂ) : StripExpType (pairReflectionFactor ds es b c hc sign) :=
  (StripExpType.const sign).mul (realEpsilon_stripExpType (realPairBlocks ds es) b c hc)

/-- The explicit ordinary weight for a real pair. -/
def ordinaryWeight (ds es : List RealBlock) (b : ℝˣ) (c : ℝ≥0) (hc : 0 < c) (sign : ℂ)
    (rate B : ℝ) : ℝ → ℂ :=
  mellinInv 0 (gaussianOrdinaryTransform (realPairLFactor ds es).denominator
    (pairReflectionFactor ds es b c hc sign) rate B)

/-- The explicit reflected weight for a real pair with reflected lists `dds`, `ees`. -/
def reflectedWeight (dds ees : List RealBlock) (rate B : ℝ) : ℝ → ℂ :=
  mellinInv 0 (gaussianReflectedTransform (realPairLFactor dds ees).denominator rate B)

theorem realWeights_data (ds es dds ees : List RealBlock) (b : ℝˣ) (c : ℝ≥0) (hc : 0 < c)
    (sign : ℂ) {rate : ℝ} (hrate : 0 < rate) (B : ℝ) :
    let f := ordinaryWeight ds es b c hc sign rate B
    let fd := reflectedWeight dds ees rate B
    Measurable f ∧ Measurable fd ∧ RapidDecay f ∧ RapidDecay fd ∧
      (∀ s : ℂ, mellin f (-s) = (realPairLFactor ds es).denominator s *
        pairReflectionFactor ds es b c hc sign s * gaussianFactor rate B s) ∧
      (∀ s : ℂ, mellin fd (s - 1) = (realPairLFactor dds ees).denominator (1 - s) *
        gaussianFactor rate B s) :=
  archimedeanGaussianMellinPair _ _ _ _ _ hrate (realPairLFactor ds es).entire
    (realPairLFactor _ _).entire (differentiable_pairReflectionFactor ds es b c hc sign)
    (realLFactor_stripExpType _) (realLFactor_stripExpType _)
    (stripExpType_pairReflectionFactor ds es b c hc sign)

/-- Continuity extends the large-height exponential bounds to every point of a strip. -/
theorem stripExpType_of_hasStripExponentialGrowth {F : ℂ → ℂ} (hF : Continuous F)
    (h : HasStripExponentialGrowth F) : StripExpType F :=
  ComplexWeightedKernelReflection.stripExpType_of_hasStripExponentialGrowth hF h

/-- The Gaussian determinant-weight identity for real kernels given a normalized reflection with
strip growth. -/
def RealWeightedKernelReflectionStatement : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (K : ℂ → X → ℂ) (L : ℂ → Y → ℂ) (δ : X → ℝ) (η : Y → ℝ),
    Measurable δ → Measurable η → (∀ x, 0 < δ x) → (∀ y, 0 < η y) →
    (∀ s x, K s x = K 0 x * (δ x : ℂ) ^ s) → (∀ s y, L s y = L 0 y * (η y : ℂ) ^ s) →
    (∃ σ : ℝ, ∀ s : ℂ, σ < s.re → Integrable (K s) μ ∧ Integrable (L s) ν) →
    ∀ (ds es dds ees : List RealBlock) (b : ℝˣ) (c : ℝ≥0) (hc : 0 < c) (sign : ℂ),
    HasRealPairNormalizedGrowth ds es dds ees b c hc sign (fun s => ∫ x, K s x ∂μ)
      (fun s => ∫ y, L s y ∂ν) →
    ∀ (rate B : ℝ), 0 < rate → ∀ {β : ℝ}, 0 < β →
      theta μ (K 0) δ (ordinaryWeight ds es b c hc sign rate B) β =
        (β : ℂ) * theta ν (L 0) η (reflectedWeight dds ees rate B) β⁻¹

set_option maxHeartbeats 650000 in
theorem realWeightedKernelReflection : RealWeightedKernelReflectionStatement.{u, v} := by
  intro X Y _ _ μ ν _ _ K L δ η hδ hη hδ₀ hη₀ hK hL hConv ds es dds ees b c hc sign hNorm rate B hrate β hb
  obtain ⟨N, Nd, hN, _, hNt, _, ⟨τ, hR⟩, hFE⟩ := hNorm
  obtain ⟨σ₀, hI⟩ := hConv
  let σ := max (max σ₀ τ) 1 + 1
  have hσ₀ : σ₀ < σ := by
    dsimp only [σ]
    linarith [le_max_left σ₀ τ, le_max_left (max σ₀ τ) (1 : ℝ)]
  have hστ : τ < σ := by
    dsimp only [σ]
    linarith [le_max_right σ₀ τ, le_max_left (max σ₀ τ) (1 : ℝ)]
  have hσ : (1 : ℝ) / 2 ≤ σ := by dsimp only [σ]; linarith [le_max_right (max σ₀ τ) (1 : ℝ)]
  obtain ⟨hKσ, hLσ⟩ := hI (σ : ℂ) (by simpa using hσ₀)
  have hK₀ : AEStronglyMeasurable (K 0) μ := by
    have hm : Measurable (fun x => (δ x : ℂ) ^ (-(σ : ℂ))) := (measurable_ofReal.comp hδ).pow_const _
    exact (hKσ.aestronglyMeasurable.mul hm.aestronglyMeasurable).congr
      (ae_of_all _ fun x => (kernel_zero_eq hδ₀ hK σ x).symm)
  have hL₀ : AEStronglyMeasurable (L 0) ν := by
    have hm : Measurable (fun y => (η y : ℂ) ^ (-(σ : ℂ))) := (measurable_ofReal.comp hη).pow_const _
    exact (hLσ.aestronglyMeasurable.mul hm.aestronglyMeasurable).congr
      (ae_of_all _ fun y => (kernel_zero_eq hη₀ hL σ y).symm)
  let D := (realPairLFactor ds es).denominator
  let Dd := (realPairLFactor dds ees).denominator
  let E := pairReflectionFactor ds es b c hc sign
  let H := gaussianFactor rate B
  have hDt : StripExpType D := realLFactor_stripExpType _
  have hDdt : StripExpType Dd := realLFactor_stripExpType _
  have hE := differentiable_pairReflectionFactor ds es b c hc sign
  have hEt := stripExpType_pairReflectionFactor ds es b c hc sign
  have hNt' := stripExpType_of_hasStripExponentialGrowth hN.continuous hNt
  obtain ⟨hm, hmt⟩ := gaussianOrdinaryTransform_spec D E hrate B (realPairLFactor ds es).entire hE hDt hEt
  obtain ⟨hmd, hmdt⟩ := gaussianReflectedTransform_spec Dd hrate B (realPairLFactor _ _).entire hDdt
  refine theta_mellinInv_reflection μ ν hK₀ hL₀ hδ hη hδ₀ hη₀ hσ
    (hKσ.norm.congr (ae_of_all _ (norm_kernel hδ₀ hK σ)))
    (hLσ.norm.congr (ae_of_all _ (norm_kernel hη₀ hL σ)))
    (N := N) (Nd := Nd) (D := D) (Dd := Dd) (E := E) (H := H) ?_ ?_ hFE
    ((hN.mul hE).mul (differentiable_gaussianFactor rate B)) ?_ hm hmd hmt hmdt ?_ ?_ hb
  · intro s hs
    exact (hR s (hs ▸ hστ)).1.trans (congrArg (D s * ·) (integral_congr_ae (ae_of_all _ (hK s))))
  · intro s hs
    exact (hR s (hs ▸ hστ)).2.trans (congrArg (Dd s * ·) (integral_congr_ae (ae_of_all _ (hL s))))
  · exact (stripDecay_gaussianFactor_mul (hNt'.mul hEt) hrate B).congr fun s => mul_comm _ _
  · intro s
    simp [gaussianOrdinaryTransform, H]
  · intro s
    rw [gaussianReflectedTransform, show -(s - 1) = 1 - s by ring, show 1 + (s - 1) = s by ring]

end Langlands.Global.RankinSelbergGlobal.RealWeightedKernelReflection
