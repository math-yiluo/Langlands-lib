import Langlands.Global.RankinSelberg.RealPairedOrdinaryReflection
import Langlands.Global.RankinSelberg.RealOrdinaryBlockNormalizedGrowth
import Langlands.Global.RankinSelberg.RealOrdinaryEqualCharacterContinuation

/-! # Ordinary normalized growth for smooth pairs of real model coefficients -/

noncomputable section

open MeasureTheory Matrix
open Langlands.Archimedean Langlands.Archimedean.DerivativeSmoothVectors
open Langlands.LocalFactor.Archimedean
open scoped ContDiff Manifold Matrix.Norms.Operator NNReal SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false

namespace Langlands.Global.RankinSelbergGlobal.RealPairedRankRaising

open ArchimedeanLocal CompletedProjectiveRepresentation RealPaddedExponential
open ArchimedeanRealPairIdentity (sigmaFinite_measure sigmaFinite_rect)
open RealPaddedWhittakerProduct (oppositeScale)
open RealPairedSmoothRowAbsorption (slot)
open RealJacquet (HasRealPairNormalizedGrowth realOrdinaryBlockNormalizedGrowth)
open RealLocalJacquet (dualBlock)

attribute [local instance] archimedeanRealGLMeasurable archimedeanRealGLBorel
  archimedeanRealNMeasurable archimedeanRealNBorel archimedeanRealQMeasurable archimedeanRealQBorel

local notation "G" => fun m : ℕ => Langlands.GeneralLinear (m + 1) ℝ
local notation "N" => fun m : ℕ => Langlands.GeneralLinear.upperUnipotent (m + 1) ℝ
local notation "Mat" => fun m : ℕ => Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ
local notation "Rows" => fun m : ℕ => 𝓢(Fin (m + 1) → ℝ, ℂ)
local notation "detSign" => fun ds : List RealBlock => (RealJacquet.determinant ds (-1) : ℂ)

section Unequal

variable (r t : ℕ) (E : Fin 2 → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
  [∀ i, CompleteSpace (E i)] (R : ∀ i, G (pairRanks r t i) →* (E i →L[ℂ] E i))

local notation "n" => pairRanks r t
local notation "A" => fun i => Mat (n i)
local notation "I" => 𝓘(ℝ, (∀ i : Fin 2, A i))
local notation "P" => productAction A R
local notation "D" => DerivativeSmoothVectors I P
local notation "D₀" => fun i => DerivativeSmoothVectors 𝓘(ℝ, A i) (R i)
local notation "act" => DerivativeSmoothVectors.representation I P
local notation "pad" => fun (hm : ∀ i, t ≤ n i) => padProductGL (fun i => n i + 1) (fun i => Nat.succ_le_succ (hm i))

/-- Dense pure sources with coefficients in the prescribed real models give entire normalized
ordinary and reflected integral families on the genuine product-group smooth space. -/
def RealPairedUnequalModelGrowthStatement : Prop :=
  RealOrdinaryNormalizedContinuationStatement → (∀ i, IsContinuousRepresentation (R i)) →
  ∀ (h : t < r) (hm : ∀ i, t ≤ n i) (a : ℝˣ) (μ : RealQuotientMeasureData t)
    (L : ∀ i, D₀ i →L[ℂ] ℂ) (T : D →L[ℂ] ℂ),
    (∀ v : ∀ i, D₀ i, T (pureSmooth A R v) = ∏ i, L i (v i)) →
    (∀ (i : Fin 2) (u : N (n i)) (v : D), T (act (slot n i u.val) v) =
      realWhittakerCharacter (oppositeScale a i) u.val * T v) →
    (∀ (u : N t) (v : D), T (act (pad hm u.val) v) = T v) →
    ∀ (ds es : List RealBlock), realRank ds = r + 1 → realRank es = t + 1 →
    ∀ (F : Fin 2 → Type*) (f : ∀ i, F i → D₀ i), (∀ i, DenseRange (f i)) →
    (∀ x : ∀ i, F i,
      let v := fun i => f i (x i)
      slotCoefficient n R L v 0 ∈ realWhittakerModel r ds a ∧
        slotCoefficient n R L v 1 ∈ realWhittakerModel t es (-a)) →
    ∀ v : D, HasRealPairNormalizedGrowth ds es (ds.map dualBlock) (es.map dualBlock) (-a)
      (NNReal.sqrt ‖(a : ℝ)‖₊) (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero))
      ((detSign ds) ^ (t + 1) * detSign es)
      (ordinaryPaddedPairIntegral n E R t hm μ T (v, none))
      (fun s => ∫ p, unequalPairedDualKernel r t E R h T v s p ∂(realUnequalDualMeasure (r := r) a μ))

set_option maxHeartbeats 1200000 in
theorem realPairedUnequalModelGrowth : RealPairedUnequalModelGrowthStatement r t E R := by
  intro hO hR h hm a μ L T hT hCov hInv ds es hd he F f hDense hModel
  let c := NNReal.sqrt ‖(a : ℝ)‖₊
  have hc : 0 < c := NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)
  let sign := (detSign ds) ^ (t + 1) * detSign es
  have hSign : sign ≠ 0 := mul_ne_zero (pow_ne_zero _ (Units.ne_zero _)) (Units.ne_zero _)
  obtain ⟨σ, hI⟩ := realPairedUnequalDualConvergence r t E R hR h a T hCov μ
  have := sigmaFinite_measure μ
  have := sigmaFinite_rect (realSelfDualMeasure a) (r - (t + 1)) (t + 1)
  apply realPairedUnequalOrdinaryReflection r t E R hR h hm a μ T hCov hInv
    ds es (ds.map dualBlock) (es.map dualBlock) (-a) c hc sign hSign F f hDense
  intro x
  let v := fun i => f i (x i)
  let W : G r → ℂ := slotCoefficient n R L v 0
  let V : G t → ℂ := slotCoefficient n R L v 1
  have hW : W ∈ realUniformWhittakerModel r ds a := realWhittakerModels_eq r ds hd a ▸ (hModel x).1
  have hV : V ∈ realUniformWhittakerModel t es (-a) := realWhittakerModels_eq t es he (-a) ▸ (hModel x).2
  refine ((realOrdinaryBlockNormalizedGrowth hO).1 r t h ds es hd he a μ W V hW hV).congr (τ := σ)
    (fun s _ => ?_) (fun s hs => ?_)
  · change realUnequalIntegral h μ W V s = ∫ q, ordinaryPaddedPairKernel n E R t hm T
      (pureSmooth A R v, none) s q ∂μ.measure
    rw [(realPairedUnequalOrdinaryKernels r t R L T hT v).1 h hm s]
    rfl
  · change realUnequalDualIntegral h a μ W V s = ∫ p, unequalPairedDualKernel r t E R h T
      (pureSmooth A R v) s p ∂(realUnequalDualMeasure a μ)
    unfold realUnequalDualMeasure
    rw [integral_prod _ ((hI (pureSmooth A R v)).1 s hs), unequalPairedDualKernel_pure r t E R h T L hT]
    rfl

end Unequal

section Equal

variable (r : ℕ) (E : Fin 2 → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
  [∀ i, CompleteSpace (E i)] (R : ∀ i, G (pairRanks r r i) →* (E i →L[ℂ] E i))

local notation "n" => pairRanks r r
local notation "A" => fun i => Mat (n i)
local notation "I" => 𝓘(ℝ, (∀ i : Fin 2, A i))
local notation "P" => productAction A R
local notation "D" => DerivativeSmoothVectors I P
local notation "D₀" => fun i => DerivativeSmoothVectors 𝓘(ℝ, A i) (R i)
local notation "act" => DerivativeSmoothVectors.representation I P
local notation "pad" => fun (hm : ∀ i, r ≤ n i) => padProductGL (fun i => n i + 1) (fun i => Nat.succ_le_succ (hm i))

/-- The same dense model comparison in equal ranks keeps the Schwartz row and its Fourier
transform as the ordinary and reflected row tests. -/
def RealPairedEqualModelGrowthStatement : Prop :=
  RealOrdinaryNormalizedContinuationStatement → (∀ i, IsContinuousRepresentation (R i)) →
  ∀ (hm : ∀ i, r ≤ n i) (a : ℝˣ) (μ : RealQuotientMeasureData r)
    (L : ∀ i, D₀ i →L[ℂ] ℂ) (T : D →L[ℂ] ℂ),
    (∀ v : ∀ i, D₀ i, T (pureSmooth A R v) = ∏ i, L i (v i)) →
    (∀ (i : Fin 2) (u : N (n i)) (v : D), T (act (slot n i u.val) v) =
      realWhittakerCharacter (oppositeScale a i) u.val * T v) →
    (∀ (u : N r) (v : D), T (act (pad hm u.val) v) = T v) →
    ∀ (ds es : List RealBlock), realRank ds = r + 1 → realRank es = r + 1 →
    ∀ (F : Fin 2 → Type*) (f : ∀ i, F i → D₀ i), (∀ i, DenseRange (f i)) →
    (∀ x : ∀ i, F i,
      let v := fun i => f i (x i)
      slotCoefficient n R L v 0 ∈ realWhittakerModel r ds a ∧
        slotCoefficient n R L v 1 ∈ realWhittakerModel r es (-a)) →
    ∀ (Φ : Rows r) (v : D), HasRealPairNormalizedGrowth ds es (ds.map dualBlock) (es.map dualBlock) (-a)
      (NNReal.sqrt ‖(a : ℝ)‖₊) (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)) ((detSign ds) ^ r)
      (ordinaryPaddedPairIntegral n E R r hm μ T (v, some Φ))
      (fun s => ∫ q, equalPairedDualKernel r E R (-a) T v Φ s q ∂μ.measure)

set_option maxHeartbeats 1200000 in
theorem realPairedEqualModelGrowth : RealPairedEqualModelGrowthStatement r E R := by
  intro hO hR hm a μ L T hT hCov hInv ds es hd he F f hDense hModel Φ
  let c := NNReal.sqrt ‖(a : ℝ)‖₊
  have hc : 0 < c := NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)
  let sign := (detSign ds) ^ r
  have hSign : sign ≠ 0 := pow_ne_zero _ (Units.ne_zero _)
  apply realPairedEqualOrdinaryReflection r E R hR hm a μ T hCov hInv
    ds es (ds.map dualBlock) (es.map dualBlock) (-a) c hc sign hSign F f hDense Φ
  intro x
  let v := fun i => f i (x i)
  let W : G r → ℂ := slotCoefficient n R L v 0
  let V : G r → ℂ := slotCoefficient n R L v 1
  have hW : W ∈ realUniformWhittakerModel r ds a := realWhittakerModels_eq r ds hd a ▸ (hModel x).1
  have hV : V ∈ realUniformWhittakerModel r es (-a) := realWhittakerModels_eq r es he (-a) ▸ (hModel x).2
  refine ((realOrdinaryBlockNormalizedGrowth hO).2 r ds es hd he a μ W V Φ hW hV).congr (τ := 0)
    (fun s _ => ?_) (fun s _ => ?_)
  · change realEqualIntegral μ W V Φ s = ∫ q, ordinaryPaddedPairKernel n E R r hm T
      (pureSmooth A R v, some Φ) s q ∂μ.measure
    rw [realPairedEqualOrdinaryKernel r R L T hT v Φ hm s]
    rfl
  · change realEqualDualIntegral (-a) μ W V Φ s = ∫ q, equalPairedDualKernel r E R (-a) T (pureSmooth A R v) Φ s q ∂μ.measure
    rw [equalPairedDualKernel_pure r E R (-a) T L hT v Φ s]
    rfl

end Equal

end Langlands.Global.RankinSelbergGlobal.RealPairedRankRaising
