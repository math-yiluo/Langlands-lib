import Langlands.Global.RankinSelberg.RealPairedDualConvergence
import Langlands.Global.RankinSelberg.RealPairedOrdinaryConvergence
import Langlands.Global.RankinSelberg.RealDenseMellinReflection
import Langlands.Representation.Archimedean.SmoothProjectiveProductSources
import Langlands.Representation.Archimedean.SmoothDerivativeBasisTopology
import Langlands.Representation.Archimedean.SmoothDerivativeCompleteness
import Mathlib.Topology.Baire.CompleteMetrizable

/-! # Entire ordinary normalizations for genuine smooth real pairs -/

noncomputable section

open Matrix MeasureTheory Set TopologicalSpace
open Langlands.Archimedean Langlands.Archimedean.DerivativeSmoothVectors
open scoped ContDiff Manifold Matrix.Norms.Operator NNReal SchwartzMap Uniformity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
set_option maxHeartbeats 1200000

namespace Langlands.Global.RankinSelbergGlobal.RealPairedRankRaising

open ArchimedeanLocal CompletedProjectiveRepresentation RealPaddedExponential
open ArchimedeanRealPairIdentity (quotientDetAbs quotientDetAbs_pos detPower_eq_cpow measurable_quotientDetAbs
  sigmaFinite_measure sFinite_dualMeasure)
open RealPaddedWhittakerProduct (oppositeScale)
open RealPairedSmoothRowAbsorption (slot)
open RealPairedWhittakerGauge (coefficient)
open RealDenseMellinReflection (kernelIntegral realDenseMellinReflection)
open RealJacquet (HasRealPairNormalizedGrowth)
open RealRankRaisingIntegral (realQuotientDetPower)
open Langlands.LocalFactor.Archimedean (RealBlock)

attribute [local instance] archimedeanRealGLMeasurable archimedeanRealGLBorel
  archimedeanRealNMeasurable archimedeanRealNBorel archimedeanRealQMeasurable archimedeanRealQBorel

local notation "G" => fun m : ℕ => Langlands.GeneralLinear (m + 1) ℝ
local notation "N" => fun m : ℕ => Langlands.GeneralLinear.upperUnipotent (m + 1) ℝ
local notation "Q" => fun m : ℕ => Langlands.RankinSelberg.LeftUnipotentQuotient m ℝ
local notation "Mat" => fun m : ℕ => Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ
local notation "Rows" => fun m : ℕ => 𝓢(Fin (m + 1) → ℝ, ℂ)
local notation "wt" => fun m : ℕ => Langlands.GeneralLinear.weylInverseTranspose (m + 1) ℝ
local notation "Rect" => fun r t : ℕ => Matrix (Fin (r - (t + 1))) (Fin (t + 1)) ℝ
local notation "last" => Langlands.RankinSelberg.lastRow
local notation "dp" => ArchimedeanLocal.detPower realNormalizedAbs

private theorem detPower_sub {m : ℕ} (g : Q m) (s c : ℂ) :
    dp g.out (s - c) = dp g.out (-c) * (quotientDetAbs g : ℂ) ^ s := by
  have hn : (quotientDetAbs g : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (quotientDetAbs_pos g).ne'
  rw [detPower_eq_cpow, detPower_eq_cpow, show s - c = -c + s by ring]
  exact Complex.cpow_add _ _ hn

section Linear

variable {X Y V : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]

private theorem finite_moments_of_right_integrability (μ : Measure X) (B : X → V →L[ℂ] ℂ) (δ : X → ℝ)
    (hδm : Measurable δ) (hδ : ∀ x, 0 < δ x) (K : V → ℂ → X → ℂ)
    (hB : ∀ v s x, K v s x = B x v * (δ x : ℂ) ^ s)
    (σ : ℝ) (hI : ∀ v s, σ < (s : ℂ).re → Integrable (K v s) μ) :
    (∀ v, AEStronglyMeasurable (fun x => B x v) μ) ∧
    ∀ (τ : ℝ), σ < τ → ∀ v, Integrable (fun x => ‖B x v‖ * δ x ^ τ) μ := by
  have hm (v : V) : Integrable (K v ((σ + 1 : ℝ) : ℂ)) μ := hI _ _ (by simp)
  constructor
  · intro v
    let z : ℂ := (σ + 1 : ℝ)
    have hMeas : AEStronglyMeasurable (fun x => (δ x : ℂ) ^ (-z)) μ :=
      ((Complex.measurable_ofReal.comp hδm).pow_const _).aestronglyMeasurable
    refine ((hm v).aestronglyMeasurable.mul hMeas).congr (ae_of_all _ fun x => ?_)
    change K v z x * (δ x : ℂ) ^ (-z) = B x v
    rw [hB, mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (hδ x).ne'),
      add_neg_cancel, Complex.cpow_zero, mul_one]
  · intro τ hτ v
    refine (hI v (τ : ℂ) (by simpa using hτ)).norm.congr (ae_of_all _ fun x => ?_)
    change ‖K v (τ : ℂ) x‖ = ‖B x v‖ * δ x ^ τ
    rw [hB, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hδ x), Complex.ofReal_re]

private theorem normalizedGrowth_of_dense_integrable
    [IsTopologicalAddGroup V] [SequentialSpace V] [BarrelledSpace ℂ V]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (B : X → V →L[ℂ] ℂ) (Bd : Y → V →L[ℂ] ℂ) (δ : X → ℝ) (δd : Y → ℝ)
    (hδm : Measurable δ) (hδdm : Measurable δd) (hδ : ∀ x, 0 < δ x) (hδd : ∀ x, 0 < δd x)
    (K : V → ℂ → X → ℂ) (Kd : V → ℂ → Y → ℂ)
    (hB : ∀ v s x, K v s x = B x v * (δ x : ℂ) ^ s)
    (hBd : ∀ v s x, Kd v s x = Bd x v * (δd x : ℂ) ^ s)
    (σ σd : ℝ) (hI : ∀ v s, σ < (s : ℂ).re → Integrable (K v s) μ)
    (hId : ∀ v s, σd < (s : ℂ).re → Integrable (Kd v s) ν)
    (ds es dds ees : List RealBlock) (b : ℝˣ) (c : ℝ≥0) (hc : 0 < c) (sign : ℂ) (hsign : sign ≠ 0)
    (A₀ : Set V) (hDense : Dense (Submodule.span ℂ A₀ : Set V))
    (hInit : ∀ v ∈ A₀, HasRealPairNormalizedGrowth ds es dds ees b c hc sign
      (fun s => ∫ x, K v s x ∂μ) (fun s => ∫ x, Kd v s x ∂ν)) :
    ∀ v, HasRealPairNormalizedGrowth ds es dds ees b c hc sign
      (fun s => ∫ x, K v s x ∂μ) (fun s => ∫ x, Kd v s x ∂ν) := by
  obtain ⟨hM, hP⟩ := finite_moments_of_right_integrability μ B δ hδm hδ K hB σ hI
  obtain ⟨hMd, hPd⟩ := finite_moments_of_right_integrability ν Bd δd hδdm hδd Kd hBd σd hId
  have hMom : ∃ bound : ℝ, ∀ τ : ℝ, bound ≤ τ → ∀ v,
      Integrable (fun x => ‖B x v‖ * δ x ^ τ) μ ∧ Integrable (fun y => ‖Bd y v‖ * δd y ^ τ) ν := by
    refine ⟨max σ σd + 1, fun τ hτ v => ⟨hP τ ?_ v, hPd τ ?_ v⟩⟩
    · exact (le_max_left _ _).trans_lt ((lt_add_one _).trans_le hτ)
    · exact (le_max_right _ _).trans_lt ((lt_add_one _).trans_le hτ)
  have he v s : (∫ x, K v s x ∂μ) = kernelIntegral μ B δ v s := integral_congr_ae (ae_of_all _ (hB v s))
  have hed v s : (∫ x, Kd v s x ∂ν) = kernelIntegral ν Bd δd v s := integral_congr_ae (ae_of_all _ (hBd v s))
  have hAll := realDenseMellinReflection (V := V) μ ν B Bd δ δd hδm hδdm hδ hδd hM hMd hMom
    ds es dds ees b c hc sign hsign A₀ hDense (fun v hv => (hInit v hv).congr (τ := 0)
      (fun s _ => he v s) (fun s _ => hed v s))
  intro v
  exact (hAll v).congr (τ := 0) (fun s _ => (he v s).symm) (fun s _ => (hed v s).symm)

end Linear

section Ordinary

variable (n : Fin 2 → ℕ) (E : Fin 2 → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
  (R : ∀ i, G (n i) →* (E i →L[ℂ] E i))

local notation "A" => fun i => Mat (n i)
local notation "I" => 𝓘(ℝ, (∀ i : Fin 2, A i))
local notation "P" => productAction A R
local notation "D" => DerivativeSmoothVectors I P
local notation "U" => (∀ i : Fin 2, A i)ˣ

private def weightedCoefficientCLM (T : D →L[ℂ] ℂ) (g : U) (z : ℂ) : D →L[ℂ] ℂ :=
  z • T.comp (SmoothAction.derivativeAction I P g)

private theorem weightedCoefficientCLM_apply (T : D →L[ℂ] ℂ) (g : U) (z : ℂ) (v : D) :
    weightedCoefficientCLM n E R T g z v = z * T (DerivativeSmoothVectors.representation I P g v) := rfl

private def ordinaryKernelBase (m : ℕ) (hm : ∀ i, m ≤ n i) (T : D →L[ℂ] ℂ)
    (Φ : Option (Rows m)) (q : Q m) : D →L[ℂ] ℂ :=
  weightedCoefficientCLM n E R T (padProductGL (fun i => n i + 1) (fun i => Nat.succ_le_succ (hm i)) q.out)
    (Φ.elim 1 (fun φ => φ (last q.out)) * dp q.out (-pairedDetShift n m))

private theorem ordinaryKernel_eq_base (m : ℕ) (hm : ∀ i, m ≤ n i) (T : D →L[ℂ] ℂ)
    (Φ : Option (Rows m)) (v : D) (s : ℂ) (q : Q m) :
    ordinaryPaddedPairKernel n E R m hm T (v, Φ) s q =
      ordinaryKernelBase n E R m hm T Φ q v * (quotientDetAbs q : ℂ) ^ s := by
  unfold ordinaryPaddedPairKernel paddedPairKernel realQuotientDetPower
  rw [detPower_sub]
  unfold ordinaryKernelBase paddedPairCoefficient
  rw [weightedCoefficientCLM_apply]
  ring

end Ordinary

section Unequal

variable (r t : ℕ) (E : Fin 2 → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
  (R : ∀ i, G (pairRanks r t i) →* (E i →L[ℂ] E i))

local notation "n" => pairRanks r t
local notation "A" => fun i => Mat (n i)
local notation "I" => 𝓘(ℝ, (∀ i : Fin 2, A i))
local notation "P" => productAction A R
local notation "D" => DerivativeSmoothVectors I P
local notation "D₀" => fun i => DerivativeSmoothVectors 𝓘(ℝ, A i) (R i)
local notation "act" => DerivativeSmoothVectors.representation I P
local notation "pad" => fun (hm : ∀ i, t ≤ n i) => padProductGL (fun i => n i + 1) (fun i => Nat.succ_le_succ (hm i))

private def unequalDualKernelBase (h : t < r) (T : D →L[ℂ] ℂ) (p : Q t × Rect r t) : D →L[ℂ] ℂ :=
  weightedCoefficientCLM n E R T
    (slot n 1 (wt t p.1.out) * slot n 0
      (wt r (ArchimedeanLocal.rectangularPoint h p.1.out p.2 * ArchimedeanLocal.unfoldingWeyl h)))
    (dp p.1.out (-(((r - t : ℕ) : ℂ) / 2)))

private theorem unequalDualKernel_eq_base (h : t < r) (T : D →L[ℂ] ℂ) (v : D) (s : ℂ) (p : Q t × Rect r t) :
    unequalPairedDualKernel r t E R h T v s p =
      unequalDualKernelBase r t E R h T p v * (quotientDetAbs p.1 : ℂ) ^ s := by
  unfold unequalPairedDualKernel
  rw [detPower_sub]
  unfold unequalDualKernelBase unequalDualPairCoefficient reflectedPairCoefficient coefficient
  rw [weightedCoefficientCLM_apply]
  ring

variable [∀ i, CompleteSpace (E i)]

/-- Genuine smooth normalized reflection at unequal ranks from the pair equation on dense pure
sources of the two individual smooth spaces. -/
def RealPairedUnequalOrdinaryReflectionStatement : Prop :=
  (∀ i, IsContinuousRepresentation (R i)) →
  ∀ (h : t < r) (hm : ∀ i, t ≤ n i) (a : ℝˣ) (μ : RealQuotientMeasureData t) (T : D →L[ℂ] ℂ),
    (∀ (i : Fin 2) (u : N (n i)) (v : D), T (act (slot n i u.val) v) =
      realWhittakerCharacter (oppositeScale a i) u.val * T v) →
    (∀ (u : N t) (v : D), T (act (pad hm u.val) v) = T v) →
    ∀ (ds es dds ees : List RealBlock) (b : ℝˣ) (c : ℝ≥0) (hc : 0 < c) (sign : ℂ), sign ≠ 0 →
    ∀ (F : Fin 2 → Type*) (f : ∀ i, F i → D₀ i), (∀ i, DenseRange (f i)) →
    (∀ x : ∀ i, F i, let v := pureSmooth A R (fun i => f i (x i));
      HasRealPairNormalizedGrowth ds es dds ees b c hc sign
        (ordinaryPaddedPairIntegral n E R t hm μ T (v, none))
        (fun s => ∫ p, unequalPairedDualKernel r t E R h T v s p ∂(realUnequalDualMeasure (r := r) a μ))) →
    ∀ v : D, HasRealPairNormalizedGrowth ds es dds ees b c hc sign
      (ordinaryPaddedPairIntegral n E R t hm μ T (v, none))
      (fun s => ∫ p, unequalPairedDualKernel r t E R h T v s p ∂(realUnequalDualMeasure (r := r) a μ))

set_option maxHeartbeats 1300000 in
theorem realPairedUnequalOrdinaryReflection : RealPairedUnequalOrdinaryReflectionStatement r t E R := by
  intro hR h hm a μ T hCov hInv ds es dds ees b c hc sign hSign F f hDense hPure
  have hP := isContinuous_productAction A R hR
  let : CompleteSpace D := completeSpace_of_isContinuousRepresentation_units P hP
  let : MetrizableSpace D := metrizableSpace_of_finiteDimensional I P
  let : (𝓤 D).IsCountablyGenerated := by rw [uniformity_eq_comap_nhds_zero]; infer_instance
  let : BaireSpace D := inferInstance
  let μd := realUnequalDualMeasure (r := r) a μ
  have := sigmaFinite_measure μ
  have : SFinite μd := sFinite_dualMeasure a μ
  obtain ⟨σ, hI⟩ := realPairedOrdinaryConvergence n E R hR a T t hm μ hCov hInv
  obtain ⟨σd, hId⟩ := realPairedUnequalDualConvergence r t E R hR h a T hCov μ
  let C := range (fun x : ∀ i, F i => pureSmooth A R (fun i => f i (x i)))
  have hSpan : Dense (Submodule.span ℂ C : Set D) := smoothProjectiveProductSources A R hR F f hDense
  exact normalizedGrowth_of_dense_integrable μ.measure μd (ordinaryKernelBase n E R t hm T none)
    (unequalDualKernelBase r t E R h T) quotientDetAbs (fun p => quotientDetAbs p.1)
    measurable_quotientDetAbs (measurable_quotientDetAbs.comp measurable_fst) quotientDetAbs_pos
    (fun p => quotientDetAbs_pos p.1) (fun v => ordinaryPaddedPairKernel n E R t hm T (v, none))
    (unequalPairedDualKernel r t E R h T) (ordinaryKernel_eq_base n E R t hm T none)
    (unequalDualKernel_eq_base r t E R h T) σ σd
    (fun v s hs => (hI (v, none) (Or.inr ⟨0, h⟩)).1 s hs) (fun v s hs => (hId v).1 s hs)
    ds es dds ees b c hc sign hSign C hSpan (by rintro _ ⟨x, rfl⟩; exact hPure x)

end Unequal

section Equal

variable (r : ℕ) (E : Fin 2 → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
  (R : ∀ i, G (pairRanks r r i) →* (E i →L[ℂ] E i))

local notation "n" => pairRanks r r
local notation "A" => fun i => Mat (n i)
local notation "I" => 𝓘(ℝ, (∀ i : Fin 2, A i))
local notation "P" => productAction A R
local notation "D" => DerivativeSmoothVectors I P
local notation "D₀" => fun i => DerivativeSmoothVectors 𝓘(ℝ, A i) (R i)
local notation "act" => DerivativeSmoothVectors.representation I P
local notation "pad" => fun (hm : ∀ i, r ≤ n i) => padProductGL (fun i => n i + 1) (fun i => Nat.succ_le_succ (hm i))

private def equalDualKernelBase (b : ℝˣ) (T : D →L[ℂ] ℂ) (Φ : Rows r) (q : Q r) : D →L[ℂ] ℂ :=
  weightedCoefficientCLM n E R T
    (slot n 1 (wt r q.out) * slot n 0 (wt r (q.out * 1))) (realFourierTransform b Φ (last q.out))

private theorem equalDualKernel_eq_base (b : ℝˣ) (T : D →L[ℂ] ℂ) (Φ : Rows r) (v : D) (s : ℂ) (q : Q r) :
    equalPairedDualKernel r E R b T v Φ s q =
      equalDualKernelBase r E R b T Φ q v * (quotientDetAbs q : ℂ) ^ s := by
  unfold equalPairedDualKernel equalDualKernelBase reflectedPairCoefficient coefficient
  rw [detPower_eq_cpow, weightedCoefficientCLM_apply]
  rw [mul_comm (realFourierTransform b Φ (last q.out))]
  rfl

variable [∀ i, CompleteSpace (E i)]

/-- Genuine smooth normalized reflection at equal ranks from dense pure sources, with a Schwartz row. -/
def RealPairedEqualOrdinaryReflectionStatement : Prop :=
  (∀ i, IsContinuousRepresentation (R i)) →
  ∀ (hm : ∀ i, r ≤ n i) (a : ℝˣ) (μ : RealQuotientMeasureData r) (T : D →L[ℂ] ℂ),
    (∀ (i : Fin 2) (u : N (n i)) (v : D), T (act (slot n i u.val) v) =
      realWhittakerCharacter (oppositeScale a i) u.val * T v) →
    (∀ (u : N r) (v : D), T (act (pad hm u.val) v) = T v) →
    ∀ (ds es dds ees : List RealBlock) (b : ℝˣ) (c : ℝ≥0) (hc : 0 < c) (sign : ℂ), sign ≠ 0 →
    ∀ (F : Fin 2 → Type*) (f : ∀ i, F i → D₀ i), (∀ i, DenseRange (f i)) → ∀ Φ : Rows r,
    (∀ x : ∀ i, F i, let v := pureSmooth A R (fun i => f i (x i));
      HasRealPairNormalizedGrowth ds es dds ees b c hc sign
        (ordinaryPaddedPairIntegral n E R r hm μ T (v, some Φ))
        (fun s => ∫ q, equalPairedDualKernel r E R b T v Φ s q ∂μ.measure)) →
    ∀ v : D, HasRealPairNormalizedGrowth ds es dds ees b c hc sign
      (ordinaryPaddedPairIntegral n E R r hm μ T (v, some Φ))
      (fun s => ∫ q, equalPairedDualKernel r E R b T v Φ s q ∂μ.measure)

set_option maxHeartbeats 1300000 in
theorem realPairedEqualOrdinaryReflection : RealPairedEqualOrdinaryReflectionStatement r E R := by
  intro hR hm a μ T hCov hInv ds es dds ees b c hc sign hSign F f hDense Φ hPure
  have hP := isContinuous_productAction A R hR
  let : CompleteSpace D := completeSpace_of_isContinuousRepresentation_units P hP
  let : MetrizableSpace D := metrizableSpace_of_finiteDimensional I P
  let : (𝓤 D).IsCountablyGenerated := by rw [uniformity_eq_comap_nhds_zero]; infer_instance
  let : BaireSpace D := inferInstance
  have := sigmaFinite_measure μ
  obtain ⟨σ, hI⟩ := realPairedOrdinaryConvergence n E R hR a T r hm μ hCov hInv
  obtain ⟨σd, hId⟩ := realPairedEqualDualConvergence r E R hR a b T hCov μ
  let C := range (fun x : ∀ i, F i => pureSmooth A R (fun i => f i (x i)))
  have hSpan : Dense (Submodule.span ℂ C : Set D) := smoothProjectiveProductSources A R hR F f hDense
  exact normalizedGrowth_of_dense_integrable μ.measure μ.measure (ordinaryKernelBase n E R r hm T (some Φ))
    (equalDualKernelBase r E R b T Φ) quotientDetAbs quotientDetAbs
    measurable_quotientDetAbs measurable_quotientDetAbs quotientDetAbs_pos quotientDetAbs_pos
    (fun v => ordinaryPaddedPairKernel n E R r hm T (v, some Φ)) (fun v => equalPairedDualKernel r E R b T v Φ)
    (ordinaryKernel_eq_base n E R r hm T (some Φ)) (equalDualKernel_eq_base r E R b T Φ) σ σd
    (fun v s hs => (hI (v, some Φ) (Or.inl (by simp))).1 s hs) (fun v s hs => (hId v Φ).1 s hs)
    ds es dds ees b c hc sign hSign C hSpan (by rintro _ ⟨x, rfl⟩; exact hPure x)

end Equal

end Langlands.Global.RankinSelbergGlobal.RealPairedRankRaising
