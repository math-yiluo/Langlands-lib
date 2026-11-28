import Langlands.Global.RankinSelberg.RealPairedExactExtraction

/-! # Continuous Schwartz row evaluations for exact real equal-rank tests -/

noncomputable section

open MeasureTheory Langlands.Archimedean Langlands.LocalFactor.Archimedean
open scoped ContDiff Manifold Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal RealStandardCompactBanach RealPairedStandardModels RealPairedRankRaising
open RealPaddedWhittakerProduct (oppositeScale)
open RealOrdinaryTestExtraction (coefficient)

attribute [local instance] archimedeanRealGLMeasurable archimedeanRealGLBorel
  archimedeanRealNMeasurable archimedeanRealNBorel archimedeanRealQMeasurable archimedeanRealQBorel

private local instance (n : ℕ) (ds : List RealBlock) : NormedAddCommGroup (Carrier n ds) :=
  (closureSubmodule (n := n) ds).normedAddCommGroup

private local instance (n : ℕ) (ds : List RealBlock) : NormedSpace ℂ (Carrier n ds) :=
  (closureSubmodule (n := n) ds).normedSpace

/-- With exact ordinary continuation, the normalized equal-rank value for two fixed
compact-finite coefficients is a continuous linear evaluation in its Schwartz row. -/
def RealOrdinaryEqualRowEvaluationStatement : Prop :=
  RealOrdinaryNormalizedContinuationStatement →
    ∀ (r : ℕ) (ds es : List RealBlock), realRank ds = r + 1 → realRank es = r + 1 →
      ∀ (a : ℝˣ) (μ : RealQuotientMeasureData r) (W : realWhittakerModel r ds a)
        (V : realWhittakerModel r es (-a)),
        HasContinuousOrdinaryNormalizationFamily (fun Φ => realOrdinaryEqualTest r ds es a μ (W, V, Φ))
          (realPairLFactor ds es)

set_option maxHeartbeats 1100000 in
theorem realOrdinaryEqualRowEvaluation : RealOrdinaryEqualRowEvaluationStatement := by
  intro hO r ds es hd he a μ W V
  let n := pairRanks r r
  let bs := pairLists ds es
  let E := slotCarrier n bs
  let R := slotRepresentation n bs
  let A (i : Fin 2) := Matrix (Fin (n i + 1)) (Fin (n i + 1)) ℝ
  let : ChartedSpace (∀ i, A i) (∀ i, A i)ˣ :=
    (Units.isOpenEmbedding_val (R := ∀ i, A i)).singletonChartedSpace
  let F (i : Fin 2) := Automorphic.realStandardKFinite (n i + 1) (bs i)
  have hRank (i : Fin 2) : realRank (bs i) = n i + 1 := by fin_cases i <;> assumption
  have hm (i : Fin 2) : r ≤ n i := by fin_cases i <;> exact le_rfl
  have hR (i : Fin 2) : IsContinuousRepresentation (R i) := isContinuousRepresentation (bs i)
  obtain ⟨B, L, T, hData, hPair⟩ := realPairedStandardModels n bs hRank a
  have rangeMem (X : Langlands.GeneralLinear (r + 1) ℝ → ℂ)
      {P Q : Submodule ℂ (Langlands.GeneralLinear (r + 1) ℝ → ℂ)} (h : P = Q) (hx : X ∈ P) : X ∈ Q :=
    h ▸ hx
  have hW := rangeMem W (show realWhittakerModel r ds a = (B 0).range from (hData 0).2.2.2) W.property
  have hV := rangeMem V (show realWhittakerModel r es (-a) = (B 1).range from (hData 1).2.2.2) V.property
  obtain ⟨f₀, hf₀⟩ := hW
  obtain ⟨f₁, hf₁⟩ := hV
  let f : ∀ i, F i := Fin.cons f₀ (Fin.cons f₁ (fun j => Fin.elim0 j))
  have hW' : coefficient (B 0) (hData 0).1 (f 0) = W := Subtype.ext hf₀
  have hV' : coefficient (B 1) (hData 1).1 (f 1) = V := Subtype.ext hf₁
  have hEq : (fun Φ => ordinaryPaddedPairIntegral n E R r hm μ T (pairedCompactVector n bs f, some Φ)) =
      fun Φ => realOrdinaryEqualTest r ds es a μ (W, V, Φ) := by
    funext Φ
    rw [pairedCompactEqualIntegral r ds es a B (fun i => (hData i).1) L (fun i => (hData i).2.1) T hPair hm μ f Φ,
      hW', hV']
  have hN : HasEntireOrdinaryNormalizations (fun Φ => realOrdinaryEqualTest r ds es a μ (W, V, Φ))
      (realPairLFactor ds es) := fun Φ => hO.2 r ds es hd he a μ (W, V, Φ)
  rw [← hEq] at hN ⊢
  exact (realPairedNormalizedEvaluation n E R hR a T r hm μ hPair.2.1 (hPair.2.2 r hm)
    (realPairLFactor ds es) (ArchimedeanRealPairFactor.realLFactor_ne_zero (realPairBlocks ds es))).2
      (pairedCompactVector n bs f) hN

end Langlands.Global.RankinSelbergGlobal
