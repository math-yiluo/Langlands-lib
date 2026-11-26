import Langlands.Global.RankinSelberg.ArchimedeanMellinConvolutionReflection
import Langlands.Global.RankinSelberg.RealWeightedKernelReflection
import Langlands.Global.RankinSelberg.RealLocalEqualNormalizedFactors

/-! # Convolved real gap weights -/

noncomputable section

open scoped NNReal

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealGapMellinWeights

open Langlands.LocalFactor (ReciprocalEntire)
open Langlands.LocalFactor.Archimedean
open ArchimedeanMellinPair (RapidDecay mellinConvolution archimedeanBinaryMellinConvolution)
open ArchimedeanRealPairIdentity (rapidDecay_const_mul)
open ArchimedeanInverseMellin (gaussianFactor)
open RealJacquet (realPairLFactor_cons_mul)
open RealWeightedKernelReflection (ordinaryWeight reflectedWeight realWeights_data
  pairReflectionFactor)

variable (c : ℝ≥0) (hc : 0 < c)

/-- The larger-rank ordinary radial weight: the logarithmic convolution of the smaller pair
weight, multiplied by a constant phase, with the weight of the adjoined block. -/
def gapOrdinaryWeight (phase : ℂ) (d : RealBlock) (ds es : List RealBlock) (b₁ b₂ : ℝˣ)
    (sign₁ sign₂ : ℂ) : ℝ → ℂ :=
  mellinConvolution (fun x => phase * ordinaryWeight ds es b₁ c hc sign₁ (1 / 2) 0 x)
    (ordinaryWeight [d] es b₂ c hc sign₂ (1 / 2) 0)

/-- The larger-rank reflected radial weight. -/
def gapReflectedWeight (dd : RealBlock) (dds ees : List RealBlock) : ℝ → ℂ :=
  mellinConvolution (reflectedWeight dds ees (1 / 2) 0) (reflectedWeight [dd] ees (1 / 2) 0)

private theorem gaussianFactor_half_sq (s : ℂ) :
    gaussianFactor (1 / 2) 0 s * gaussianFactor (1 / 2) 0 s = Complex.exp (s ^ 2) := by
  unfold gaussianFactor
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The two half-rate Gaussian pairs combine into the full Gaussian pair for the larger rank,
whenever the phase and the two reflection factors multiply to the reflection factor of the
enlarged list. -/
def RealGapMellinWeightsStatement : Prop :=
  ∀ (c : ℝ≥0) (hc : 0 < c) (phase : ℂ) (d dd : RealBlock) (ds es dds ees : List RealBlock)
    (b b₁ b₂ : ℝˣ) (sign sign₁ sign₂ : ℂ),
    (∀ s : ℂ, phase * pairReflectionFactor ds es b₁ c hc sign₁ s *
      pairReflectionFactor [d] es b₂ c hc sign₂ s = pairReflectionFactor (d :: ds) es b c hc sign s) →
    let f := gapOrdinaryWeight c hc phase d ds es b₁ b₂ sign₁ sign₂
    let fd := gapReflectedWeight dd dds ees
    Measurable f ∧ Measurable fd ∧ RapidDecay f ∧ RapidDecay fd ∧
      (∀ s : ℂ, mellin f (-s) = (realPairLFactor (d :: ds) es).denominator s *
        pairReflectionFactor (d :: ds) es b c hc sign s * Complex.exp (s ^ 2)) ∧
      (∀ s : ℂ, mellin fd (s - 1) = (realPairLFactor (dd :: dds) ees).denominator (1 - s) *
        Complex.exp (s ^ 2))

theorem realGapMellinWeights : RealGapMellinWeightsStatement := by
  intro c hc phase d dd ds es dds ees b b₁ b₂ sign sign₁ sign₂ hE
  let f₁ := ordinaryWeight ds es b₁ c hc sign₁ (1 / 2) 0
  let f₂ := ordinaryWeight [d] es b₂ c hc sign₂ (1 / 2) 0
  let k₁ := reflectedWeight dds ees (1 / 2) 0
  let k₂ := reflectedWeight [dd] ees (1 / 2) 0
  obtain ⟨hf₁, hk₁, hdf₁, hdk₁, hf₁M, hk₁M⟩ :=
    realWeights_data ds es dds ees b₁ c hc sign₁ (rate := 1 / 2) (by norm_num) 0
  obtain ⟨hf₂, hk₂, hdf₂, hdk₂, hf₂M, hk₂M⟩ :=
    realWeights_data [d] es [dd] ees b₂ c hc sign₂ (rate := 1 / 2) (by norm_num) 0
  obtain ⟨hf, hdf, hfM⟩ := archimedeanBinaryMellinConvolution (fun x => phase * f₁ x) f₂
    (hf₁.const_mul phase) hf₂ (rapidDecay_const_mul hdf₁ phase) hdf₂
  obtain ⟨hk, hdk, hkM⟩ := archimedeanBinaryMellinConvolution k₁ k₂ hk₁ hk₂ hdk₁ hdk₂
  refine ⟨hf, hk, hdf, hdk, fun s => ?_, fun s => ?_⟩
  · have hphase : mellin (fun x => phase * f₁ x) (-s) = phase * mellin f₁ (-s) := by
      simpa only [smul_eq_mul] using (mellin_const_smul f₁ (-s) phase)
    change mellin (mellinConvolution (fun x => phase * f₁ x) f₂) (-s) = _
    have h₁ : mellin f₁ (-s) = _ := hf₁M s
    have h₂ : mellin f₂ (-s) = _ := hf₂M s
    rw [hfM, hphase, h₁, h₂, realPairLFactor_cons_mul d ds es, ReciprocalEntire.denominator_mul,
      ← hE s, ← gaussianFactor_half_sq]
    ring
  · change mellin (mellinConvolution k₁ k₂) (s - 1) = _
    have h₁ : mellin k₁ (s - 1) = _ := hk₁M s
    have h₂ : mellin k₂ (s - 1) = _ := hk₂M s
    rw [hkM, h₁, h₂, ← gaussianFactor_half_sq, realPairLFactor_cons_mul dd dds ees,
      ReciprocalEntire.denominator_mul]
    ring

end Langlands.Global.RankinSelbergGlobal.RealGapMellinWeights
