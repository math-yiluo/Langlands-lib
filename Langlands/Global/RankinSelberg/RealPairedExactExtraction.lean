import Langlands.Global.RankinSelberg.RealPairedStandardModels
import Langlands.Global.RankinSelberg.RealPairedNormalizedEvaluation

/-! # Exact ordinary tests from nonzero paired smooth values -/

noncomputable section

open MeasureTheory Set Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open Langlands.Archimedean
open scoped ContDiff Manifold Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false

namespace Langlands.Global.RankinSelbergGlobal

/-- Equal integral functions have the same normalization, with the value unchanged. -/
def OrdinaryIntegralNormalization.congrIntegral {I J L : ℂ → ℂ}
    (N : OrdinaryIntegralNormalization I L) (h : I = J) : OrdinaryIntegralNormalization J L :=
  ⟨N.value, N.analytic, h ▸ N.eq_on_right⟩

/-- An ordinary normalized value is nonzero at the specified spectral parameter. -/
def HasNonzeroOrdinaryNormalizationAt {X : Type*} (Z : X → ℂ → ℂ) (L : ReciprocalEntire) (s : ℂ) : Prop :=
  ∃ (x : X) (N : OrdinaryIntegralNormalization (Z x) (fun z => (L.denominator z)⁻¹)), N.value s ≠ 0

/-- The normalized evaluation of a continuous family detects a dense span on its generators. -/
theorem HasContinuousOrdinaryNormalizationFamily.detects_dense_span
    {V F : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    {Z : V → ℂ → ℂ} {L : ReciprocalEntire}
    (h : HasContinuousOrdinaryNormalizationFamily Z L)
    (hN : HasEntireOrdinaryNormalizations Z L) (j : F → V)
    (hDense : Dense (Submodule.span ℂ (range j) : Set V)) (s : ℂ)
    (hs : HasNonzeroOrdinaryNormalizationAt Z L s) :
    HasNonzeroOrdinaryNormalizationAt (Z ∘ j) L s := by
  obtain ⟨A, hA, hCont⟩ := h
  obtain ⟨v, N, hne⟩ := hs
  let T : V →L[ℂ] ℂ := ⟨(LinearMap.proj s).comp A, hCont s⟩
  by_contra hzero
  have hSpan : Submodule.span ℂ (range j) ≤ T.ker := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, rfl⟩
    obtain ⟨M⟩ := hN (j f)
    by_contra hf
    apply hzero
    refine ⟨f, M, ?_⟩
    rw [hA]
    exact hf
  have hv : v ∈ T.ker := T.isClosed_ker.closure_subset_iff.mpr hSpan (hDense v)
  apply hne
  rw [hA]
  exact hv

namespace RealPairedStandardModels

open ArchimedeanLocal RealStandardCompactBanach RealPairedRankRaising CompletedProjectiveRepresentation
open RealPaddedWhittakerProduct (oppositeScale)
open RealOrdinaryTestExtraction (coefficient smoothOfCompact)

attribute [local instance] archimedeanRealGLMeasurable archimedeanRealGLBorel
  archimedeanRealNMeasurable archimedeanRealNBorel archimedeanRealQMeasurable archimedeanRealQBorel

private local instance (n : ℕ) (ds : List RealBlock) : NormedAddCommGroup (Carrier n ds) :=
  (closureSubmodule (n := n) ds).normedAddCommGroup

private local instance (n : ℕ) (ds : List RealBlock) : NormedSpace ℂ (Carrier n ds) :=
  (closureSubmodule (n := n) ds).normedSpace

local notation "G" => fun m : ℕ => Langlands.GeneralLinear (m + 1) ℝ
local notation "Rows" => fun m : ℕ => 𝓢(Fin (m + 1) → ℝ, ℂ)

section Unequal

variable (r t : ℕ) (ds es : List RealBlock) (a : ℝˣ)

local notation "n" => pairRanks r t
local notation "blocks" => pairLists ds es
local notation "Alg" => (∀ i : Fin 2, Matrix (Fin (n i + 1)) (Fin (n i + 1)) ℝ)

private local instance : ChartedSpace Alg Algˣ :=
  (Units.isOpenEmbedding_val (R := Alg)).singletonChartedSpace

local notation "E" => slotCarrier n blocks
local notation "R₀" => slotRepresentation n blocks
local notation "J" => PairSmooth n blocks
local notation "F" => fun i => Automorphic.realStandardKFinite (n i + 1) (blocks i)
local notation "Coef" => ∀ i, F i →ₗ[ℂ] (G (n i) → ℂ)
local notation "Fnc" => ∀ i, SlotSmooth n blocks i →L[ℂ] ℂ
local notation "hExact" => fun (B : Coef) =>
  ∀ i, IsRealWhittakerIntertwiner (n i) (blocks i) (oppositeScale a i) (B i)
local notation "hEval" => fun (B : Coef) (L : Fnc) =>
  ∀ i, IsWhittakerStandardEvaluation (blocks i) (oppositeScale a i) (B i) (L i)
local notation "Lpair" => realPairLFactor ds es

set_option maxHeartbeats 800000 in
/-- The paired integral on the compact-finite source equals the exact ordinary unequal test. -/
theorem pairedCompactUnequalIntegral
    (B : Coef) (hB : hExact B) (L : Fnc) (hL : hEval B L) (T : J →L[ℂ] ℂ)
    (hT : IsPairedStandardForm n blocks a L T) (h : t < r) (hm : ∀ i, t ≤ n i) (μ : RealQuotientMeasureData t)
    (f : ∀ i, F i) :
    ordinaryPaddedPairIntegral n E R₀ t hm μ T (pairedCompactVector n blocks f, none) =
      realOrdinaryUnequalTest h ds es a μ (coefficient (B 0) (hB 0) (f 0), coefficient (B 1) (hB 1) (f 1)) := by
  funext z
  have he := (realPairedUnequalOrdinaryKernels r t R₀ L T hT.1 (fun i => smoothOfCompact (blocks i) (f i))).1 h hm z
  rw [slotCoefficient_of_compact n blocks a B L hL f 0,
    slotCoefficient_of_compact n blocks a B L hL f 1] at he
  change (∫ q, ordinaryPaddedPairKernel n E R₀ t hm T (pairedCompactVector n blocks f, none) z q ∂μ.measure) =
    ∫ q, realUnequalIntegrand h (B 0 (f 0)) (B 1 (f 1)) z q ∂μ.measure
  rw [he]

/-- Continuous paired normalized values detect the actual compact-finite unequal-rank tests. -/
def RealPairedUnequalExactExtractionStatement : Prop :=
  ∀ (B : Coef) (L : Fnc) (T : J →L[ℂ] ℂ),
  hExact B → hEval B L → IsPairedStandardForm n blocks a L T →
  ∀ (h : t < r) (hm : ∀ i, t ≤ n i) (μ : RealQuotientMeasureData t),
    let Z := fun v => ordinaryPaddedPairIntegral n E R₀ t hm μ T (v, none)
    HasEntireOrdinaryNormalizations Z Lpair → HasContinuousOrdinaryNormalizationFamily Z Lpair →
    ∀ s, HasNonzeroOrdinaryNormalizationAt Z Lpair s →
      HasNonzeroOrdinaryNormalizationAt (realOrdinaryUnequalTest h ds es a μ) Lpair s

set_option maxHeartbeats 850000 in
theorem realPairedUnequalExactExtraction : RealPairedUnequalExactExtractionStatement r t ds es a := by
  intro B L T hB hL hT h hm μ Z hN hCont s hs
  obtain ⟨f, N, hne⟩ := hCont.detects_dense_span hN (pairedCompactVector n blocks)
    (dense_span_pairedCompactVector n blocks) s hs
  let w := (coefficient (B 0) (hB 0) (f 0), coefficient (B 1) (hB 1) (f 1))
  change OrdinaryIntegralNormalization (ordinaryPaddedPairIntegral n E R₀ t hm μ T
    (pairedCompactVector n blocks f, none)) (fun z => ((Lpair).denominator z)⁻¹) at N
  exact ⟨w, N.congrIntegral (pairedCompactUnequalIntegral r t ds es a B hB L hL T hT h hm μ f), hne⟩

end Unequal

section Equal

variable (r : ℕ) (ds es : List RealBlock) (a : ℝˣ)

local notation "n" => pairRanks r r
local notation "blocks" => pairLists ds es
local notation "Alg" => (∀ i : Fin 2, Matrix (Fin (n i + 1)) (Fin (n i + 1)) ℝ)

private local instance : ChartedSpace Alg Algˣ :=
  (Units.isOpenEmbedding_val (R := Alg)).singletonChartedSpace

local notation "E" => slotCarrier n blocks
local notation "R₀" => slotRepresentation n blocks
local notation "J" => PairSmooth n blocks
local notation "F" => fun i => Automorphic.realStandardKFinite (n i + 1) (blocks i)
local notation "Coef" => ∀ i, F i →ₗ[ℂ] (G (n i) → ℂ)
local notation "Fnc" => ∀ i, SlotSmooth n blocks i →L[ℂ] ℂ
local notation "hExact" => fun (B : Coef) =>
  ∀ i, IsRealWhittakerIntertwiner (n i) (blocks i) (oppositeScale a i) (B i)
local notation "hEval" => fun (B : Coef) (L : Fnc) =>
  ∀ i, IsWhittakerStandardEvaluation (blocks i) (oppositeScale a i) (B i) (L i)
local notation "Lpair" => realPairLFactor ds es

set_option maxHeartbeats 800000 in
/-- The paired integral on the compact-finite source equals the exact ordinary equal test. -/
theorem pairedCompactEqualIntegral
    (B : Coef) (hB : hExact B) (L : Fnc) (hL : hEval B L) (T : J →L[ℂ] ℂ)
    (hT : IsPairedStandardForm n blocks a L T) (hm : ∀ i, r ≤ n i) (μ : RealQuotientMeasureData r)
    (f : ∀ i, F i) (Φ : Rows r) :
    ordinaryPaddedPairIntegral n E R₀ r hm μ T (pairedCompactVector n blocks f, some Φ) =
      realOrdinaryEqualTest r ds es a μ (coefficient (B 0) (hB 0) (f 0), coefficient (B 1) (hB 1) (f 1), Φ) := by
  funext z
  have he := realPairedEqualOrdinaryKernel r R₀ L T hT.1 (fun i => smoothOfCompact (blocks i) (f i)) Φ hm z
  rw [slotCoefficient_of_compact n blocks a B L hL f 0,
    slotCoefficient_of_compact n blocks a B L hL f 1] at he
  change (∫ q, ordinaryPaddedPairKernel n E R₀ r hm T (pairedCompactVector n blocks f, some Φ) z q ∂μ.measure) =
    ∫ q, realEqualIntegrand (B 0 (f 0)) (B 1 (f 1)) Φ z q ∂μ.measure
  rw [he]

/-- Continuous paired normalized values detect the actual compact-finite equal-rank tests. -/
def RealPairedEqualExactExtractionStatement : Prop :=
  ∀ (B : Coef) (L : Fnc) (T : J →L[ℂ] ℂ),
  hExact B → hEval B L → IsPairedStandardForm n blocks a L T →
  ∀ (hm : ∀ i, r ≤ n i) (μ : RealQuotientMeasureData r) (Φ : Rows r),
    let Z := fun v => ordinaryPaddedPairIntegral n E R₀ r hm μ T (v, some Φ)
    HasEntireOrdinaryNormalizations Z Lpair → HasContinuousOrdinaryNormalizationFamily Z Lpair →
    ∀ s, HasNonzeroOrdinaryNormalizationAt Z Lpair s →
      HasNonzeroOrdinaryNormalizationAt (realOrdinaryEqualTest r ds es a μ) Lpair s

set_option maxHeartbeats 850000 in
theorem realPairedEqualExactExtraction : RealPairedEqualExactExtractionStatement r ds es a := by
  intro B L T hB hL hT hm μ Φ Z hN hCont s hs
  obtain ⟨f, N, hne⟩ := hCont.detects_dense_span hN (pairedCompactVector n blocks)
    (dense_span_pairedCompactVector n blocks) s hs
  let w := (coefficient (B 0) (hB 0) (f 0), coefficient (B 1) (hB 1) (f 1), Φ)
  change OrdinaryIntegralNormalization (ordinaryPaddedPairIntegral n E R₀ r hm μ T
    (pairedCompactVector n blocks f, some Φ)) (fun z => ((Lpair).denominator z)⁻¹) at N
  exact ⟨w, N.congrIntegral (pairedCompactEqualIntegral r ds es a B hB L hL T hT hm μ f Φ), hne⟩

end Equal

end RealPairedStandardModels
end Langlands.Global.RankinSelbergGlobal
