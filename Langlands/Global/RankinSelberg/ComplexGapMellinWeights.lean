import Langlands.Global.RankinSelberg.ArchimedeanMellinConvolutionReflection
import Langlands.Global.RankinSelberg.ComplexWeightedKernelReflection

/-! # Convolved complex gap weights and the adjoining central sign -/

noncomputable section

open scoped NNReal

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapMellinWeights

open Langlands.LocalFactor (ReciprocalEntire)
open Langlands.LocalFactor.Archimedean
open ArchimedeanMellinPair (RapidDecay mellinConvolution archimedeanBinaryMellinConvolution)
open ArchimedeanRealPairIdentity (rapidDecay_const_mul)
open ArchimedeanInverseMellin (gaussianFactor)
open ComplexJacquet (complexCentralSign_sq pair_epsilon_neg)
open ComplexWeightedKernelReflection (ordinaryWeight reflectedWeight complexWeights_data pairReflectionFactor)

/-- The central value of the adjoining character raised to the smaller rank. -/
def adjoiningPhase (d : ComplexCharacterData) (es : List ComplexCharacterData) : ℂ :=
  (d.character ((-1 : ℂˣ) ^ es.length) : ℂ)

private theorem adjoiningPhase_eq (d : ComplexCharacterData) (es : List ComplexCharacterData) :
    adjoiningPhase d es = complexCentralSign [d] ^ es.length := by
  simp [adjoiningPhase, complexCentralSign, map_pow, Units.val_pow_eq_pow_val]

private theorem pairLFactor_cons (d : ComplexCharacterData) (ds es : List ComplexCharacterData) :
    complexPairLFactor (d :: ds) es = (complexPairLFactor [d] es).mul (complexPairLFactor ds es) := by
  simpa only [complexPairLFactor, complexPairBlocks, List.flatMap_cons, List.flatMap_nil, List.append_nil] using
    complexLFactor_append (es.map d.mul) (complexPairBlocks ds es)

private theorem pairEpsilon_cons (d : ComplexCharacterData) (ds es : List ComplexCharacterData)
    (a : ℂˣ) (c : NNReal) (hc : 0 < c) (s : ℂ) :
    complexPairEpsilon (d :: ds) es a c hc s = complexPairEpsilon [d] es a c hc s * complexPairEpsilon ds es a c hc s := by
  simpa only [complexPairEpsilon, complexPairBlocks, List.flatMap_cons, List.flatMap_nil, List.append_nil] using
    complexEpsilon_append (es.map d.mul) (complexPairBlocks ds es) a c hc s

/-- The opposite sign of the square Fourier character accounts for the adjoining phase. -/
theorem pairReflectionFactor_cons (r : ℕ) (d : ComplexCharacterData) (ds es : List ComplexCharacterData)
    (a : ℂˣ) (s : ℂ) :
    pairReflectionFactor (d :: ds) es (-a) (complexCentralSign es ^ (r + 1)) s =
      adjoiningPhase d es * pairReflectionFactor ds es (-a) (complexCentralSign es ^ r) s *
        pairReflectionFactor [d] es a 1 s := by
  unfold pairReflectionFactor
  simp only [Units.val_neg, nnnorm_neg, one_mul]
  rw [pairEpsilon_cons, Units.val_mul, pair_epsilon_neg [d] es a, List.length_singleton, pow_one,
    ← adjoiningPhase_eq]
  let E := (complexPairEpsilon ds es (-a) ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) s : ℂ)
  let F := (complexPairEpsilon [d] es a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) s : ℂ)
  let ω := complexCentralSign es
  let c := adjoiningPhase d es
  change ω ^ (r + 1) * ((c * ω * F) * E) = c * (ω ^ r * E) * F
  calc
    _ = (ω ^ r * (c * E * F)) * ω ^ 2 := by rw [pow_succ]; ring
    _ = _ := by rw [show ω ^ 2 = 1 from complexCentralSign_sq es, mul_one]; ring

/-- The larger-rank ordinary radial weight, including the adjoining phase. -/
def gapOrdinaryWeight (r : ℕ) (d : ComplexCharacterData) (ds es : List ComplexCharacterData) (a : ℂˣ) : ℝ → ℂ :=
  mellinConvolution (fun x => adjoiningPhase d es * ordinaryWeight ds es (-a) (complexCentralSign es ^ r) (1 / 2) 0 x)
    (ordinaryWeight [d] es a 1 (1 / 2) 0)

/-- The larger-rank reflected radial weight. -/
def gapReflectedWeight (d : ComplexCharacterData) (ds es : List ComplexCharacterData) : ℝ → ℂ :=
  mellinConvolution (reflectedWeight ds es (1 / 2) 0) (reflectedWeight [d] es (1 / 2) 0)

private theorem gaussianFactor_half_sq (s : ℂ) :
    gaussianFactor (1 / 2) 0 s * gaussianFactor (1 / 2) 0 s = Complex.exp (s ^ 2) := by
  unfold gaussianFactor
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The two half-rate Gaussian pairs combine into the full Gaussian pair for the larger rank. -/
def ComplexGapMellinWeightsStatement : Prop :=
  ∀ (r : ℕ) (d : ComplexCharacterData) (ds es : List ComplexCharacterData) (a : ℂˣ),
    let f := gapOrdinaryWeight r d ds es a
    let fd := gapReflectedWeight d ds es
    Measurable f ∧ Measurable fd ∧ RapidDecay f ∧ RapidDecay fd ∧
      (∀ s : ℂ, mellin f (-s) = (complexPairLFactor (d :: ds) es).denominator s *
        pairReflectionFactor (d :: ds) es (-a) (complexCentralSign es ^ (r + 1)) s * Complex.exp (s ^ 2)) ∧
      (∀ s : ℂ, mellin fd (s - 1) = (complexPairLFactor ((d :: ds).map ComplexCharacterData.inv)
        (es.map ComplexCharacterData.inv)).denominator (1 - s) * Complex.exp (s ^ 2))

theorem complexGapMellinWeights : ComplexGapMellinWeightsStatement := by
  intro r d ds es a
  let f₁ := ordinaryWeight ds es (-a) (complexCentralSign es ^ r) (1 / 2) 0
  let f₂ := ordinaryWeight [d] es a 1 (1 / 2) 0
  let k₁ := reflectedWeight ds es (1 / 2) 0
  let k₂ := reflectedWeight [d] es (1 / 2) 0
  let phase := adjoiningPhase d es
  obtain ⟨hf₁, hk₁, hdf₁, hdk₁, hf₁M, hk₁M⟩ :=
    complexWeights_data ds es (-a) (complexCentralSign es ^ r) (rate := 1 / 2) (by norm_num) 0
  obtain ⟨hf₂, hk₂, hdf₂, hdk₂, hf₂M, hk₂M⟩ :=
    complexWeights_data [d] es a 1 (rate := 1 / 2) (by norm_num) 0
  obtain ⟨hf, hdf, hfM⟩ := archimedeanBinaryMellinConvolution (fun x => phase * f₁ x) f₂
    (hf₁.const_mul phase) hf₂ (rapidDecay_const_mul hdf₁ phase) hdf₂
  obtain ⟨hk, hdk, hkM⟩ := archimedeanBinaryMellinConvolution k₁ k₂ hk₁ hk₂ hdk₁ hdk₂
  refine ⟨hf, hk, hdf, hdk, fun s => ?_, fun s => ?_⟩
  · have hphase : mellin (fun x => phase * f₁ x) (-s) = phase * mellin f₁ (-s) := by
      simpa only [smul_eq_mul] using (mellin_const_smul f₁ (-s) phase)
    change mellin (mellinConvolution (fun x => phase * f₁ x) f₂) (-s) = _
    have h₁ : mellin f₁ (-s) = _ := hf₁M s
    have h₂ : mellin f₂ (-s) = _ := hf₂M s
    rw [hfM, hphase, h₁, h₂, pairLFactor_cons d ds es, ReciprocalEntire.denominator_mul, pairReflectionFactor_cons,
      ← gaussianFactor_half_sq]
    unfold phase
    ring
  · change mellin (mellinConvolution k₁ k₂) (s - 1) = _
    have h₁ : mellin k₁ (s - 1) = _ := hk₁M s
    have h₂ : mellin k₂ (s - 1) = _ := hk₂M s
    rw [hkM, h₁, h₂, ← gaussianFactor_half_sq]
    simp only [List.map_cons, List.map_nil,
      pairLFactor_cons d.inv (ds.map ComplexCharacterData.inv) (es.map ComplexCharacterData.inv),
      ReciprocalEntire.denominator_mul]
    ring

end Langlands.Global.RankinSelbergGlobal.ComplexGapMellinWeights
