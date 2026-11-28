import Langlands.Global.RankinSelberg.RealCompactParabolicPrimal
import Langlands.Global.RankinSelberg.RealOrdinaryEqualRowEvaluation

/-! # Pointwise detection from a leading real block at or above the comparison rank -/

noncomputable section

open MeasureTheory TopologicalSpace Langlands.Archimedean Langlands.LocalFactor.Archimedean
open scoped ContDiff Distributions Manifold Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal CompletedProjectiveRepresentation RealStandardCompactBanach
open RealExactBlockStandardEvaluation RealExactWhittakerUniqueness RealParabolicCompactSection
open RealPairedStandardModels RealPairedRankRaising
open RealOrdinaryTestExtraction (smoothOfCompact)

attribute [local instance] archimedeanRealGLMeasurable archimedeanRealGLBorel
  archimedeanRealNMeasurable archimedeanRealNBorel archimedeanRealQMeasurable archimedeanRealQBorel

private local instance (n : ℕ) (ds : List RealBlock) : NormedAddCommGroup (Carrier n ds) :=
  (closureSubmodule (n := n) ds).normedAddCommGroup

private local instance (n : ℕ) (ds : List RealBlock) : NormedSpace ℂ (Carrier n ds) :=
  (closureSubmodule (n := n) ds).normedSpace

local notation "G" => fun r => Langlands.GeneralLinear (r + 1) ℝ
local notation "S" => fun r ds => realStandardModule (r + 1) ds
local notation "X" => fun m p => Matrix (Fin (m + 1)) (Fin (p + 1)) ℝ
local notation "Test" => fun m p => 𝓓((⊤ : Opens (X m p)), ℂ)
local notation "L[" ds "," es "]" => realPairLFactor ds es

/-- Choose a nonzero smooth standard evaluation with a smooth preimage for each exact
compact-finite coefficient. -/
theorem exists_realStandardWhittakerEvaluation (r : ℕ) (ds : List RealBlock)
    (hd : realRank ds = r + 1) (a : ℝˣ) :
    ∃ L : DerivativeSmoothVectors (matrixModel ℝ (r + 1)) (representation (n := r + 1) ds) →L[ℂ] ℂ,
      IsSmoothWhittakerEvaluation ds a L ∧ L ≠ 0 ∧
        ∀ W : realWhittakerModel r ds a, ∃ f : S r ds, smoothStandardCoefficient ds L f = (W : G r → ℂ) := by
  obtain ⟨B, hB, hBn⟩ := realExactBlockWhittakerNonzero r ds hd a
  obtain ⟨L, hL⟩ := realExactBlockStandardEvaluation r ds hd a B hB
  refine ⟨L, hL.2, ?_, ?_⟩
  · intro he
    apply hBn
    apply LinearMap.ext
    intro f
    funext g
    rw [← hL.1 f g, he]
    rfl
  · intro W
    have hw : (W : G r → ℂ) ∈ B.range := realWhittakerModel_eq_range ds hd a B hB hBn ▸ W.property
    obtain ⟨f, hf⟩ := hw
    refine ⟨⟨f.val, f.property.1⟩, ?_⟩
    rw [← hf]
    exact funext (hL.1 f)

/-- If the leading block rank is at least the uncut rank, a nonzero normalized lower
ordinary test lifts to a nonzero exact upper unequal-rank test whenever the complementary
denominator is nonzero. -/
def RealOrdinaryLeadingDetectionStatement : Prop :=
  RealOrdinaryNormalizedContinuationStatement →
  ∀ (m p t : ℕ) (ht : t ≤ m) (d₁ d₂ es : List RealBlock),
    realRank d₁ = m + 1 → realRank d₂ = p + 1 → realRank es = t + 1 →
    ∀ (a : ℝˣ) (μ : RealQuotientMeasureData t) (s : ℂ),
      (L[d₂, es]).denominator s ≠ 0 →
      (∀ h : t < m, HasNonzeroOrdinaryNormalizationAt (realOrdinaryUnequalTest h d₁ es a μ) L[d₁, es] s) →
      (t = m → HasNonzeroOrdinaryNormalizationAt (realOrdinaryEqualTest t d₁ es a μ) L[d₁, es] s) →
      HasNonzeroOrdinaryNormalizationAt
        (realOrdinaryUnequalTest (show t < p + 1 + m by omega) (d₂ ++ d₁) es a μ) L[d₂ ++ d₁, es] s

set_option maxHeartbeats 1350000 in
theorem realOrdinaryLeadingDetection : RealOrdinaryLeadingDetectionStatement := by
  intro hO m p t ht d₁ d₂ es h₁ h₂ he a μ s hDen hStrict hEqual
  let r := p + 1 + m
  let ds := d₂ ++ d₁
  let n := pairRanks r t
  let bs := pairLists ds es
  let E := slotCarrier n bs
  let ρ := slotRepresentation n bs
  let A (i : Fin 2) := Matrix (Fin (n i + 1)) (Fin (n i + 1)) ℝ
  let : ChartedSpace (∀ i, A i) (∀ i, A i)ˣ :=
    (Units.isOpenEmbedding_val (R := ∀ i, A i)).singletonChartedSpace
  have hr : t < r := by dsimp [r]; omega
  have hd : realRank ds = r + 1 := by
    dsimp [r, ds]
    rw [realRank_append, h₁, h₂]
    omega
  have hRank (i : Fin 2) : realRank (bs i) = n i + 1 := by fin_cases i <;> assumption
  have hm (i : Fin 2) : t ≤ n i := by
    fin_cases i
    · exact hr.le
    · exact le_rfl
  have hρ (i : Fin 2) : IsContinuousRepresentation (ρ i) := isContinuousRepresentation (bs i)
  obtain ⟨B, L, T, hData, hPair⟩ := realPairedStandardModels n bs hRank a
  obtain ⟨L₁, hL₁, hL₁ne, hPre⟩ := exists_realStandardWhittakerEvaluation m d₁ h₁ a
  obtain ⟨L₂, hL₂, hL₂ne, _⟩ := exists_realStandardWhittakerEvaluation p d₂ h₂ a
  obtain ⟨g, τ, _, hCutEqual, hCutStrict⟩ := realCompactParabolicPrimal m p d₁ d₂ h₁ h₂ a
    (L 0) L₁ L₂ (hData 0).2.1.2 hL₁ hL₂ (hData 0).2.2.1 hL₁ne hL₂ne
  have hlift : ∃ (f : S m d₁) (V : realWhittakerModel t es (-a)) (φ : Test m p)
      (M : OrdinaryIntegralNormalization (realUnequalIntegral hr μ (compactLiftCoefficient h₁ h₂ (L 0) f g φ) V)
        (fun z => ((L[ds, es]).denominator z)⁻¹)), M.value s ≠ 0 := by
    rcases lt_or_eq_of_le ht with hlt | heq
    · obtain ⟨⟨W, V⟩, N, hN⟩ := hStrict hlt
      obtain ⟨f, hf⟩ := hPre W
      have hI : realOrdinaryUnequalTest hlt d₁ es a μ (W, V) =
          realUnequalIntegral hlt μ (smoothStandardCoefficient d₁ L₁ f) V := by
        simp only [realOrdinaryUnequalTest, hf]
      obtain ⟨M, hM⟩ := hCutStrict t hlt f es V μ (N.congrIntegral hI)
      exact ⟨f, V, τ, M, (hM s).symm ▸ mul_ne_zero hDen hN⟩
    · cases heq
      obtain ⟨⟨W, V, Ψ⟩, N, hN⟩ := hEqual rfl
      obtain ⟨F, hF, hCont⟩ := realOrdinaryEqualRowEvaluation hO m d₁ es h₁ he a μ W V
      let Λ : 𝓢((Fin (m + 1) → ℝ), ℂ) →L[ℂ] ℂ :=
        ⟨(LinearMap.proj s).comp F, hCont s⟩
      have hΛ : Λ ≠ 0 := by
        intro hz
        apply hN
        have hval : N.value s = Λ Ψ := congrFun (hF Ψ N) s
        rw [hval, hz, zero_apply]
      obtain ⟨φ, hφ⟩ := exists_compactProfile_eval_ne_zero (p := p) a Λ hΛ
      let Φ := compactRowProfile a φ
      obtain ⟨M₀⟩ := hO.2 m d₁ es h₁ he a μ (W, V, Φ)
      have hM₀ : M₀.value s ≠ 0 := (congrFun (hF Φ M₀) s).symm ▸ hφ
      obtain ⟨f, hf⟩ := hPre W
      have hI : realOrdinaryEqualTest m d₁ es a μ (W, V, Φ) =
          realEqualIntegral μ (smoothStandardCoefficient d₁ L₁ f) V Φ := by
        simp only [realOrdinaryEqualTest, hf]
      obtain ⟨M, hM⟩ := hCutEqual f φ es V μ (M₀.congrIntegral hI)
      exact ⟨f, V, φ, M, (hM s).symm ▸ mul_ne_zero hDen hM₀⟩
  obtain ⟨f, V, φ, M, hM⟩ := hlift
  have hV : (V : G t → ℂ) ∈ (B 1).range :=
    (show realWhittakerModel t es (-a) = (B 1).range from (hData 1).2.2.2) ▸ V.property
  obtain ⟨v, hv⟩ := hV
  let w : ∀ i, SlotSmooth n bs i :=
    Fin.cons (smoothSectionVector h₁ h₂ f g φ) (Fin.cons (smoothOfCompact es v) (fun i => Fin.elim0 i))
  have hw₀ : slotCoefficient n ρ L w 0 = compactLiftCoefficient h₁ h₂ (L 0) f g φ := rfl
  have hw₁ : slotCoefficient n ρ L w 1 = (V : G t → ℂ) := (funext ((hData 1).2.1.1 v)).trans hv
  let Z (v : PairSmooth n bs) := ordinaryPaddedPairIntegral n E ρ t hm μ T (v, none)
  have hI : Z (pureSmooth A ρ w) = realUnequalIntegral hr μ (compactLiftCoefficient h₁ h₂ (L 0) f g φ) V := by
    funext z
    have he := (realPairedUnequalOrdinaryKernels r t ρ L T hPair.1 w).1 hr hm z
    rw [hw₀, hw₁] at he
    change (∫ q, ordinaryPaddedPairKernel n E ρ t hm T (pureSmooth A ρ w, none) z q ∂μ.measure) =
      ∫ q, realUnequalIntegrand hr (compactLiftCoefficient h₁ h₂ (L 0) f g φ) V z q ∂μ.measure
    rw [he]
  have hG := realPairedStandardUnequalGrowth r t ds es hO hr hd he a μ hm B L T
    (fun i => (hData i).1) (fun i => (hData i).2.1) hPair
  have hN : HasEntireOrdinaryNormalizations Z L[ds, es] := fun v => (hG v).ordinaryNormalization
  have hCont := (realPairedNormalizedEvaluation n E ρ hρ a T t hm μ hPair.2.1 (hPair.2.2 t hm)
    L[ds, es] (ArchimedeanRealPairFactor.realLFactor_ne_zero (realPairBlocks ds es))).1 none (Or.inr ⟨0, hr⟩) hN
  exact realPairedUnequalExactExtraction r t ds es a B L T (fun i => (hData i).1) (fun i => (hData i).2.1)
    hPair hr hm μ hN hCont s ⟨pureSmooth A ρ w, M.congrIntegral hI.symm, hM⟩

end Langlands.Global.RankinSelbergGlobal
