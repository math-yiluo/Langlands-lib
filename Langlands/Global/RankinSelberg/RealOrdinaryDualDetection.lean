import Langlands.Global.RankinSelberg.RealGodementRowFourierInversion
import Langlands.Global.RankinSelberg.RealPairedExactExtraction
import Langlands.Global.RankinSelberg.RealPairedNormalizedReflection
import Langlands.Global.RankinSelberg.RealUniformWhittakerBlockDual

/-! # Pointwise detection after reflection of ordinary real tests -/

noncomputable section

open MeasureTheory Langlands.Archimedean Langlands.LocalFactor.Archimedean
open scoped ContDiff Manifold Matrix.Norms.Operator NNReal SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal RealStandardCompactBanach RealPairedStandardModels RealPairedRankRaising
open RealLocalJacquet (dualBlock)
open RealJacquet (realOrdinaryBlockNormalizedGrowth)
open RealOrdinaryTestExtraction (smoothOfCompact)
open RealPaddedWhittakerProduct (oppositeScale)
open RealGodement (realRowSchwartzFourier realRowSchwartzFourier_apply realRowSchwartzFourier_neg_comp)

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] archimedeanRealGLMeasurable archimedeanRealGLBorel
  archimedeanRealNMeasurable archimedeanRealNBorel archimedeanRealQMeasurable archimedeanRealQBorel

private local instance (n : ℕ) (ds : List RealBlock) : NormedAddCommGroup (Carrier n ds) :=
  (closureSubmodule (n := n) ds).normedAddCommGroup

private local instance (n : ℕ) (ds : List RealBlock) : NormedSpace ℂ (Carrier n ds) :=
  (closureSubmodule (n := n) ds).normedSpace

local notation "L[" ds "," es "]" => realPairLFactor ds es
local notation "dSign" => fun ds : List RealBlock => (RealJacquet.determinant ds (-1) : ℂ)
local notation:max "dual" ds:max => List.map dualBlock ds
local notation:max "Irr[" m "," ds "]" => IsIrreducibleGKModule (realStandardRep (m + 1) ds) (realStandardLie (m + 1) ds)

private theorem dualFunction_twice {n : ℕ} (w : Langlands.GeneralLinear n ℝ → ℂ) :
    ArchimedeanLocal.dualFunction n (ArchimedeanLocal.dualFunction n w) = w := by
  funext g
  exact congrArg w (Langlands.GeneralLinear.weylInverseTranspose_involutive n ℝ g)

private theorem dualFunction_mem_primal {r : ℕ} {ds : List RealBlock}
    (hd : realRank ds = r + 1) (hi : Irr[r, ds]) (a : ℝˣ)
    {W : Langlands.GeneralLinear (r + 1) ℝ → ℂ} (hW : W ∈ realWhittakerModel r (dual ds) (-a)) :
    ArchimedeanLocal.dualFunction (r + 1) W ∈ realWhittakerModel r ds a := by
  apply ((realBlockWhittakerDual r ds hd hi).2 a _).1
  rwa [dualFunction_twice]

/-- A nonzero normalized value of a dual block test at `1 - s` gives a nonzero value
at `s` of an exact ordinary test of the original pair. -/
def RealOrdinaryDualDetectionStatement : Prop :=
  RealOrdinaryNormalizedContinuationStatement →
  (∀ (r t : ℕ) (h : t < r) (ds es : List RealBlock), realRank ds = r + 1 → realRank es = t + 1 →
    Irr[r, ds] → Irr[t, es] → ∀ (a : ℝˣ) (μ : RealQuotientMeasureData t) (s : ℂ),
      HasNonzeroOrdinaryNormalizationAt (realOrdinaryUnequalTest h (dual ds) (dual es) (-a) μ)
        L[dual ds, dual es] (1 - s) →
      HasNonzeroOrdinaryNormalizationAt (realOrdinaryUnequalTest h ds es a μ) L[ds, es] s) ∧
  ∀ (r : ℕ) (ds es : List RealBlock), realRank ds = r + 1 → realRank es = r + 1 →
    Irr[r, ds] → Irr[r, es] → ∀ (a : ℝˣ) (μ : RealQuotientMeasureData r) (s : ℂ),
      HasNonzeroOrdinaryNormalizationAt (realOrdinaryEqualTest r (dual ds) (dual es) (-a) μ)
        L[dual ds, dual es] (1 - s) →
      HasNonzeroOrdinaryNormalizationAt (realOrdinaryEqualTest r ds es a μ) L[ds, es] s

set_option maxHeartbeats 1300000 in
theorem realOrdinaryDualDetection : RealOrdinaryDualDetectionStatement := by
  intro hO
  constructor
  · rintro r t h ds es hd he hdi hei a μ s ⟨⟨Wd, Vd⟩, Nd, hne⟩
    let n := pairRanks r t
    let bs := pairLists ds es
    let E := slotCarrier n bs
    let R := slotRepresentation n bs
    let A (i : Fin 2) := Matrix (Fin (n i + 1)) (Fin (n i + 1)) ℝ
    let : ChartedSpace (∀ i, A i) (∀ i, A i)ˣ :=
      (Units.isOpenEmbedding_val (R := ∀ i, A i)).singletonChartedSpace
    let J := PairSmooth n bs
    let F (i : Fin 2) := Automorphic.realStandardKFinite (n i + 1) (bs i)
    have hRank (i : Fin 2) : realRank (bs i) = n i + 1 := by fin_cases i <;> assumption
    have hm (i : Fin 2) : t ≤ n i := by
      fin_cases i
      · exact h.le
      · exact le_rfl
    have hR (i : Fin 2) : IsContinuousRepresentation (R i) := isContinuousRepresentation (bs i)
    obtain ⟨B, L, T, hData, hPair⟩ := realPairedStandardModels n bs hRank a
    let W := ArchimedeanLocal.dualFunction (r + 1) (Wd : Langlands.GeneralLinear (r + 1) ℝ → ℂ)
    let V := ArchimedeanLocal.dualFunction (t + 1) (Vd : Langlands.GeneralLinear (t + 1) ℝ → ℂ)
    have hW := dualFunction_mem_primal hd hdi a Wd.property
    have hV := dualFunction_mem_primal he hei (-a)
      (show (Vd : Langlands.GeneralLinear (t + 1) ℝ → ℂ) ∈ realWhittakerModel t (dual es) (-(-a)) from
        by simpa only [neg_neg] using Vd.property)
    rw [show realWhittakerModel r ds a = (B 0).range from (hData 0).2.2.2] at hW
    rw [show realWhittakerModel t es (-a) = (B 1).range from (hData 1).2.2.2] at hV
    obtain ⟨f₀, hf₀⟩ := hW
    obtain ⟨f₁, hf₁⟩ := hV
    let f : ∀ i, F i := Fin.cons f₀ (fun j => (congrArg Fin.succ (Fin.eq_zero j)).symm ▸ f₁)
    have hf₀' : B 0 (f 0) = W := hf₀
    have hf₁' : B 1 (f 1) = V := hf₁
    have hK (z : ℂ) := reflectedOrdinaryKernel_pure r t E R h T L hPair.1
      (fun i => smoothOfCompact (bs i) (f i)) z
    have hI : (fun z => ∫ q, reflectedOrdinaryKernel r t E R h T (pairedCompactVector n bs f) z q ∂μ.measure) =
        realOrdinaryUnequalTest h (dual ds) (dual es) (-a) μ (Wd, Vd) := by
      funext z
      have hh := hK z
      rw [slotCoefficient_of_compact n bs a B L (fun i => (hData i).2.1) f 0,
        slotCoefficient_of_compact n bs a B L (fun i => (hData i).2.1) f 1, hf₀', hf₁'] at hh
      change (∫ q, reflectedOrdinaryKernel r t E R h T (pairedCompactVector n bs f) z q ∂μ.measure) =
        ∫ q, realUnequalIntegrand h Wd Vd z q ∂μ.measure
      have hw : ArchimedeanLocal.dualFunction (r + 1) W = Wd := dualFunction_twice _
      have hv : ArchimedeanLocal.dualFunction (t + 1) V = Vd := dualFunction_twice _
      rw [hh, hw, hv]
    let Z (v : J) := ordinaryPaddedPairIntegral n E R t hm μ T (v, none)
    let sign := (dSign ds) ^ (t + 1) * dSign es
    have hG := realPairedStandardUnequalGrowth r t ds es hO h hd he a μ hm B L T
      (fun i => (hData i).1) (fun i => (hData i).2.1) hPair
    obtain ⟨k, u, Nu, hEq⟩ := realPairedUnequalNormalizedReflection r t E R hR h hm a μ T hPair.2.1
      ds es sign hG (pairedCompactVector n bs f)
    have hNZ : HasNonzeroOrdinaryNormalizationAt Z L[ds, es] s := by
      by_contra hz
      have hzero (i : Fin k) : (Nu i).value s = 0 := by
        by_contra hz'
        exact hz ⟨u i, Nu i, hz'⟩
      have hEq' := hEq (Nd.congrIntegral hI.symm) s
      rw [Finset.sum_eq_zero (fun i _ => hzero i), mul_zero] at hEq'
      exact hne hEq'
    have hDen := ArchimedeanRealPairFactor.realLFactor_ne_zero (realPairBlocks ds es)
    have hN : HasEntireOrdinaryNormalizations Z L[ds, es] := fun v => (hG v).ordinaryNormalization
    have hCont := (realPairedNormalizedEvaluation n E R hR a T t hm μ hPair.2.1 (hPair.2.2 t hm)
      L[ds, es] hDen).1 none (Or.inr ⟨0, h⟩) hN
    exact realPairedUnequalExactExtraction r t ds es a B L T (fun i => (hData i).1) (fun i => (hData i).2.1)
      hPair h hm μ hN hCont s hNZ
  · rintro r ds es hd he hdi hei a μ s ⟨⟨Wd, Vd, Ψ⟩, Nd, hne⟩
    have hW := dualFunction_mem_primal hd hdi a Wd.property
    have hV := dualFunction_mem_primal he hei (-a)
      (show (Vd : Langlands.GeneralLinear (r + 1) ℝ → ℂ) ∈ realWhittakerModel r (dual es) (-(-a)) from
        by simpa only [neg_neg] using Vd.property)
    let W : realWhittakerModel r ds a := ⟨_, hW⟩
    let V : realWhittakerModel r es (-a) := ⟨_, hV⟩
    let Φ := realRowSchwartzFourier (r + 1) a Ψ
    obtain ⟨N⟩ := hO.2 r ds es hd he a μ (W, V, Φ)
    have hG := (realOrdinaryBlockNormalizedGrowth hO).2 r ds es hd he a μ W V Φ
      (realWhittakerModels_eq r ds hd a ▸ W.property) (realWhittakerModels_eq r es he (-a) ▸ V.property)
    have hΦ : realFourierTransform (-a) Φ = (Ψ : (Fin (r + 1) → ℝ) → ℂ) := by
      funext x
      rw [← realRowSchwartzFourier_apply]
      change realRowSchwartzFourier (r + 1) (-a) (realRowSchwartzFourier (r + 1) a Ψ) x = Ψ x
      rw [realRowSchwartzFourier_neg_comp]
    have hI : realEqualDualIntegral (-a) μ W V Φ =
        realOrdinaryEqualTest r (dual ds) (dual es) (-a) μ (Wd, Vd, Ψ) := by
      funext z
      change ArchimedeanLocal.equalIntegral realNormalizedAbs μ.measure
        (ArchimedeanLocal.dualFunction (r + 1) (ArchimedeanLocal.dualFunction (r + 1) Wd))
        (ArchimedeanLocal.dualFunction (r + 1) (ArchimedeanLocal.dualFunction (r + 1) Vd))
        (realFourierTransform (-a) Φ) z = _
      rw [dualFunction_twice, dualFunction_twice, hΦ]
      rfl
    refine ⟨(W, V, Φ), N, fun hz => hne ?_⟩
    have hEq := hG.ordinaryNormalization_eq N (Nd.congrIntegral hI.symm) s
    rwa [hz, mul_zero] at hEq

end Langlands.Global.RankinSelbergGlobal
