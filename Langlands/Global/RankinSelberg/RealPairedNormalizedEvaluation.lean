import Langlands.Global.RankinSelberg.OrdinaryNormalizationContinuous
import Langlands.Global.RankinSelberg.RealPairedOrdinaryReflection
import Langlands.Global.RankinSelberg.SchwartzCompleteness

/-! # Continuous normalized evaluation of real paired ordinary integrals -/

noncomputable section

open MeasureTheory Set TopologicalSpace
open Langlands.Archimedean Langlands.Archimedean.DerivativeSmoothVectors Langlands.LocalFactor
open scoped ContDiff Manifold Matrix.Norms.Operator SchwartzMap Uniformity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false

namespace Langlands.Global.RankinSelbergGlobal

/-- A linear family giving the value of every entire normalization, with continuous
scalar evaluation at each spectral parameter. -/
def HasContinuousOrdinaryNormalizationFamily {V : Type*} [AddCommGroup V] [Module ℂ V]
    [TopologicalSpace V] (Z : V → ℂ → ℂ) (L : ReciprocalEntire) : Prop :=
  ∃ F : V →ₗ[ℂ] (ℂ → ℂ),
    (∀ (v : V) (N : OrdinaryIntegralNormalization (Z v) (fun s => (L.denominator s)⁻¹)), N.value = F v) ∧
    ∀ s, Continuous (fun v => F v s)

private theorem hasContinuousOrdinaryNormalizationFamily_of_kernel
    {V X : Type*} [AddCommGroup V] [Module ℂ V] [UniformSpace V]
    [IsUniformAddGroup V] [ContinuousSMul ℂ V] [SequentialSpace V] [BarrelledSpace ℂ V]
    [MeasurableSpace X] (μ : Measure X) (K : ℂ → X → V →L[ℂ] ℂ) (L : ReciprocalEntire) (σ : ℝ)
    (hL : ∃ b : ℝ, ∀ s : ℂ, b < s.re → L.denominator s ≠ 0)
    (hI : ∀ v s, σ < s.re → Integrable (fun x => K s x v) μ)
    (hHol : ∀ v, DifferentiableOn ℂ (fun s => ∫ x, K s x v ∂μ) {s : ℂ | σ < s.re})
    (hN : HasEntireOrdinaryNormalizations (fun v s => ∫ x, K s x v ∂μ) L) :
    HasContinuousOrdinaryNormalizationFamily (fun v s => ∫ x, K s x v ∂μ) L := by
  obtain ⟨F, hF, hCont⟩ := ordinaryNormalizationContinuous μ K L σ hL hI hHol hN
  obtain ⟨b, hb⟩ := hL
  refine ⟨F, fun v N => ?_, hCont⟩
  let M : OrdinaryIntegralNormalization (fun s => ∫ x, K s x v ∂μ) (fun s => (L.denominator s)⁻¹) :=
    ⟨F v, fun s _ => (hF v).1.analyticAt s, max σ b, fun s hs => by
      rw [(hF v).2 s ((le_max_left _ _).trans_lt hs), mul_comm (L.denominator s), mul_assoc,
        mul_inv_cancel₀ (hb s ((le_max_right _ _).trans_lt hs)), mul_one]⟩
  exact N.value_eq_of_factor_ne_zero M ⟨b, fun s hs => inv_ne_zero (hb s hs)⟩

namespace RealPairedRankRaising

open ArchimedeanLocal CompletedProjectiveRepresentation RealPaddedExponential
open RealPaddedWhittakerProduct (oppositeScale)
open RealPairedSmoothRowAbsorption (slot)
open RealRankRaisingIntegral (realQuotientDetPower)

attribute [local instance] archimedeanRealGLMeasurable archimedeanRealGLBorel
  archimedeanRealNMeasurable archimedeanRealNBorel archimedeanRealQMeasurable archimedeanRealQBorel

local notation "G" => fun m : ℕ => Langlands.GeneralLinear (m + 1) ℝ
local notation "U" => fun m : ℕ => Langlands.GeneralLinear.upperUnipotent (m + 1) ℝ
local notation "Q" => fun m : ℕ => Langlands.RankinSelberg.LeftUnipotentQuotient m ℝ
local notation "Mat" => fun m : ℕ => Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ
local notation "Row" => fun m : ℕ => Fin (m + 1) → ℝ
local notation "Rows" => fun m : ℕ => 𝓢(Row m, ℂ)
local notation "last" => Langlands.RankinSelberg.lastRow

variable (n : Fin 2 → ℕ) (E : Fin 2 → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
  (R : ∀ i, G (n i) →* (E i →L[ℂ] E i))

local notation "A" => fun i => Mat (n i)
local notation "Alg" => (∀ i : Fin 2, A i)
local notation "I" => 𝓘(ℝ, Alg)
local notation "P" => productAction A R
local notation "D" => DerivativeSmoothVectors I P
local notation "act" => DerivativeSmoothVectors.representation I P
local notation "pad" => fun (m : ℕ) (hm : ∀ i, m ≤ n i) =>
  padProductGL (fun i => n i + 1) (fun i => Nat.succ_le_succ (hm i))

private local instance : ChartedSpace Alg Algˣ :=
  (Units.isOpenEmbedding_val (R := Alg)).singletonChartedSpace

private def vectorKernel (m : ℕ) (hm : ∀ i, m ≤ n i) (T : D →L[ℂ] ℂ) (Φ : Option (Rows m))
    (s : ℂ) (q : Q m) : D →L[ℂ] ℂ :=
  (Φ.elim 1 (fun φ => φ (last q.out)) * realQuotientDetPower q (s - pairedDetShift n m)) •
    T.comp (SmoothAction.derivativeAction I P (pad m hm q.out))

private theorem vectorKernel_apply (m : ℕ) (hm : ∀ i, m ≤ n i) (T : D →L[ℂ] ℂ) (Φ : Option (Rows m))
    (s : ℂ) (q : Q m) (v : D) :
    vectorKernel n E R m hm T Φ s q v = ordinaryPaddedPairKernel n E R m hm T (v, Φ) s q := by
  change (_ * _) * paddedPairCoefficient n E R m hm T v q = paddedPairCoefficient n E R m hm T v q * _ * _
  ring

private def rowKernel (m : ℕ) (hm : ∀ i, m ≤ n i) (T : D →L[ℂ] ℂ) (v : D)
    (s : ℂ) (q : Q m) : Rows m →L[ℂ] ℂ :=
  (paddedPairCoefficient n E R m hm T v q * realQuotientDetPower q (s - pairedDetShift n m)) •
    (BoundedContinuousFunction.evalCLM ℂ (last q.out)).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (Row m) ℂ)

private theorem rowKernel_apply (m : ℕ) (hm : ∀ i, m ≤ n i) (T : D →L[ℂ] ℂ) (v : D)
    (s : ℂ) (q : Q m) (Φ : Rows m) :
    rowKernel n E R m hm T v s q Φ = ordinaryPaddedPairKernel n E R m hm T (v, some Φ) s q := by
  change (_ * _) * Φ (last q.out) = _ * Φ (last q.out) * _
  ring

variable [∀ i, CompleteSpace (E i)]

/-- Entire normalizations for the paired ordinary kernel form a continuous linear family in
the genuine smooth vectors for a fixed permitted row. For a fixed paired vector these
normalizations form a continuous linear family in the Schwartz row when it is supplied. -/
def RealPairedNormalizedEvaluationStatement : Prop :=
  (∀ i, IsContinuousRepresentation (R i)) →
  ∀ (a : ℝˣ) (T : D →L[ℂ] ℂ) (m : ℕ) (hm : ∀ i, m ≤ n i) (μ : RealQuotientMeasureData m),
    (∀ (i : Fin 2) (u : U (n i)) (v : D), T (act (slot n i u.val) v) =
      realWhittakerCharacter (oppositeScale a i) u.val * T v) →
    (∀ (u : U m) (v : D), T (act (pad m hm u.val) v) = T v) →
    ∀ (L : ReciprocalEntire), (∃ b : ℝ, ∀ s : ℂ, b < s.re → L.denominator s ≠ 0) →
      (∀ Φ : Option (Rows m), (Φ.isSome ∨ ∃ i, m < n i) →
        HasEntireOrdinaryNormalizations (fun v => ordinaryPaddedPairIntegral n E R m hm μ T (v, Φ)) L →
        HasContinuousOrdinaryNormalizationFamily (fun v => ordinaryPaddedPairIntegral n E R m hm μ T (v, Φ)) L) ∧
      ∀ v : D,
        HasEntireOrdinaryNormalizations (fun Φ => ordinaryPaddedPairIntegral n E R m hm μ T (v, some Φ)) L →
        HasContinuousOrdinaryNormalizationFamily (fun Φ => ordinaryPaddedPairIntegral n E R m hm μ T (v, some Φ)) L

set_option maxHeartbeats 1100000 in
theorem realPairedNormalizedEvaluation : RealPairedNormalizedEvaluationStatement n E R := by
  intro hR a T m hm μ hCov hInv L hL
  obtain ⟨σ, hConv⟩ := realPairedOrdinaryConvergence n E R hR a T m hm μ hCov hInv
  constructor
  · intro Φ hΦ hN
    have hP := isContinuous_productAction A R hR
    let : CompleteSpace D := completeSpace_of_isContinuousRepresentation_units P hP
    let : MetrizableSpace D := metrizableSpace_of_finiteDimensional I P
    let : (𝓤 D).IsCountablyGenerated := by rw [uniformity_eq_comap_nhds_zero]; infer_instance
    let : BaireSpace D := inferInstance
    have hEq (v : D) (s : ℂ) (q : Q m) := vectorKernel_apply n E R m hm T Φ s q v
    have hZ : (fun v s => ∫ q, vectorKernel n E R m hm T Φ s q v ∂μ.measure) =
        fun v => ordinaryPaddedPairIntegral n E R m hm μ T (v, Φ) := by
      funext v s
      simp only [hEq, ordinaryPaddedPairIntegral]
    rw [← hZ] at hN ⊢
    exact hasContinuousOrdinaryNormalizationFamily_of_kernel μ.measure (vectorKernel n E R m hm T Φ) L σ hL
      (fun v s hs => by simpa only [hEq] using (hConv (v, Φ) hΦ).1 s hs)
      (fun v => by rw [congrFun hZ v]; exact (hConv (v, Φ) hΦ).2) hN
  · intro v hN
    let : CompleteSpace (Rows m) := SchwartzMajorant.schwartzCompleteSpace (Row m) ℂ
    let : (𝓤 (Rows m)).IsCountablyGenerated := by rw [uniformity_eq_comap_nhds_zero]; infer_instance
    let : BaireSpace (Rows m) := inferInstance
    have hEq (Φ : Rows m) (s : ℂ) (q : Q m) := rowKernel_apply n E R m hm T v s q Φ
    have hZ : (fun Φ s => ∫ q, rowKernel n E R m hm T v s q Φ ∂μ.measure) =
        fun Φ => ordinaryPaddedPairIntegral n E R m hm μ T (v, some Φ) := by
      funext Φ s
      simp only [hEq, ordinaryPaddedPairIntegral]
    rw [← hZ] at hN ⊢
    have hRow (Φ : Rows m) : (some Φ : Option (Rows m)).isSome ∨ ∃ i, m < n i := Or.inl rfl
    exact hasContinuousOrdinaryNormalizationFamily_of_kernel μ.measure (rowKernel n E R m hm T v) L σ hL
      (fun Φ s hs => by simpa only [hEq] using (hConv (v, some Φ) (hRow Φ)).1 s hs)
      (fun Φ => by rw [congrFun hZ Φ]; exact (hConv (v, some Φ) (hRow Φ)).2) hN

end RealPairedRankRaising
end Langlands.Global.RankinSelbergGlobal
