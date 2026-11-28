import Langlands.Global.RankinSelberg.RealOrdinaryLeadingDetection
import Langlands.Global.RankinSelberg.RealPairedNormalizedReflection
import Langlands.LocalFactor.RealPairLFactorNormalization

/-! # Pointwise detection from a strict lower leading real block -/

noncomputable section

open MeasureTheory TopologicalSpace
open Langlands.Archimedean Langlands.LocalFactor.Archimedean
open scoped ContDiff Distributions Manifold Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal CompletedProjectiveRepresentation RealStandardCompactBanach
open RealExactWhittakerUniqueness RealParabolicCompactSection RealParabolicPrimalIntegral
open RealPairedStandardModels RealPairedRankRaising
open RealPairedSmoothRowAbsorption (slot unitProjection_slot_self unitProjection_slot_of_ne)
open RealPaddedWhittakerProduct (oppositeScale)
open RealOrdinaryTestExtraction (smoothOfCompact)
open Langlands.GeneralLinear (lowerTriangularSubgroup lowerTriangularSubgroup_isClosed)

attribute [local instance] archimedeanRealGLMeasurable archimedeanRealGLBorel
  archimedeanRealNMeasurable archimedeanRealNBorel archimedeanRealQMeasurable archimedeanRealQBorel

private local instance (n : ℕ) (ds : List RealBlock) : NormedAddCommGroup (Carrier n ds) :=
  (closureSubmodule (n := n) ds).normedAddCommGroup

private local instance (n : ℕ) (ds : List RealBlock) : NormedSpace ℂ (Carrier n ds) :=
  (closureSubmodule (n := n) ds).normedSpace

local notation "G" => fun r => Langlands.GeneralLinear (r + 1) ℝ
local notation "N" => fun r => Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ
local notation "S" => fun r ds => realStandardModule (r + 1) ds
local notation "Mat" => fun r => Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ
local notation "Rows" => fun r : ℕ => 𝓢(Fin (r + 1) → ℝ, ℂ)
local notation "X" => fun m p => Matrix (Fin (m + 1)) (Fin (p + 1)) ℝ
local notation "Test" => fun m p => 𝓓((⊤ : Opens (X m p)), ℂ)
local notation "Tail" => lowerTriangularSubgroup 1 ℝ
local notation "L[" ds "," es "]" => realPairLFactor ds es

private local instance : MeasurableSpace Tail := borel _
private local instance : BorelSpace Tail := ⟨rfl⟩
private local instance : LocallyCompactSpace Tail := by
  let : LocallyCompactSpace (Mat 0) := inferInstanceAs (LocallyCompactSpace (Fin 1 → Fin 1 → ℝ))
  let : LocallyCompactSpace (G 0) := Units.isOpenEmbedding_val.locallyCompactSpace
  exact (lowerTriangularSubgroup_isClosed 1).locallyCompactSpace
private local instance : SecondCountableTopology Tail := by
  let : SecondCountableTopology (Mat 0) := inferInstanceAs (SecondCountableTopology (Fin 1 → Fin 1 → ℝ))
  let : SecondCountableTopology (G 0) := Units.isOpenEmbedding_val.isInducing.secondCountableTopology
  exact Topology.IsEmbedding.subtypeVal.secondCountableTopology

private instance tailHaar_rightInvariant : (Measure.haar : Measure Tail).IsMulRightInvariant where
  map_mul_right_eq_self g := by
    have h : (· * g) = (g * ·) := by
      funext x
      apply Subtype.ext
      apply Units.ext
      ext i j
      rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
      simp [Matrix.mul_apply, mul_comm]
    rw [h]
    exact MeasureTheory.map_mul_left_eq_self (Measure.haar : Measure Tail) g

/-- Nonzero ordinary normalized value with the larger rank placed first in the integral.
The scale belongs to the first supplied list. -/
def RealOrdinaryPairHasValueAt (r t : ℕ) (ds es : List RealBlock) (a : ℝˣ)
    (μ : ∀ k, RealQuotientMeasureData k) (s : ℂ) : Prop :=
  (∀ h : t < r, HasNonzeroOrdinaryNormalizationAt (realOrdinaryUnequalTest h ds es a (μ t)) L[ds, es] s) ∧
  (∀ h : r < t, HasNonzeroOrdinaryNormalizationAt (realOrdinaryUnequalTest h es ds (-a) (μ r)) L[es, ds] s) ∧
  (r = t → HasNonzeroOrdinaryNormalizationAt (realOrdinaryEqualTest r ds es a (μ r)) L[ds, es] s)

theorem RealOrdinaryPairHasValueAt.of_unequal {r t : ℕ} {ds es : List RealBlock} {a : ℝˣ}
    {μ : ∀ k, RealQuotientMeasureData k} {s : ℂ} (h : t < r)
    (hValue : HasNonzeroOrdinaryNormalizationAt (realOrdinaryUnequalTest h ds es a (μ t)) L[ds, es] s) :
    RealOrdinaryPairHasValueAt r t ds es a μ s :=
  ⟨fun _ => hValue, fun h' => (Nat.lt_asymm h h').elim, fun e => (h.ne e.symm).elim⟩

theorem RealOrdinaryPairHasValueAt.of_equal {r : ℕ} {ds es : List RealBlock} {a : ℝˣ}
    {μ : ∀ k, RealQuotientMeasureData k} {s : ℂ}
    (hValue : HasNonzeroOrdinaryNormalizationAt (realOrdinaryEqualTest r ds es a (μ r)) L[ds, es] s) :
    RealOrdinaryPairHasValueAt r r ds es a μ s :=
  ⟨fun h => (Nat.lt_irrefl _ h).elim, fun h => (Nat.lt_irrefl _ h).elim, fun _ => hValue⟩

theorem RealOrdinaryPairHasValueAt.swap {r t : ℕ} {ds es : List RealBlock} {a : ℝˣ}
    {μ : ∀ k, RealQuotientMeasureData k} {s : ℂ} (h : RealOrdinaryPairHasValueAt r t ds es a μ s) :
    RealOrdinaryPairHasValueAt t r es ds (-a) μ s := by
  refine ⟨h.2.1, fun hlt => ?_, ?_⟩
  · rw [show -(-a) = a from neg_neg a]
    exact h.1 hlt
  · intro he
    subst t
    obtain ⟨⟨W, V, Φ⟩, H, hne⟩ := h.2.2 rfl
    let W' : realWhittakerModel r ds (-(-a)) := ⟨W, by simpa only [neg_neg] using W.property⟩
    have heq : realOrdinaryEqualTest r ds es a (μ r) (W, V, Φ) =
        realOrdinaryEqualTest r es ds (-a) (μ r) (V, W', Φ) := by
      funext z
      change (∫ q, realEqualIntegrand W V Φ z q ∂(μ r).measure) =
        ∫ q, realEqualIntegrand V W' Φ z q ∂(μ r).measure
      congr 1
      funext q
      exact congrArg (fun c : ℂ => c * Φ (Langlands.RankinSelberg.lastRow q.out) *
        ArchimedeanLocal.detPower realNormalizedAbs q.out z) (mul_comm (W.val q.out) (V.val q.out))
    change HasNonzeroOrdinaryNormalizationAt (realOrdinaryEqualTest r es ds (-a) (μ r)) L[es, ds] s
    rw [← realPairLFactor_comm ds es]
    exact ⟨(V, W', Φ), H.congrIntegral heq, hne⟩

private theorem fullCovariance (n : Fin 2 → ℕ) (bs : Fin 2 → List RealBlock) (a : ℝˣ)
    (L : ∀ i, SlotSmooth n bs i →L[ℂ] ℂ) (T : PairSmooth n bs →L[ℂ] ℂ)
    (hT : IsPairedStandardForm n bs a L T)
    (g : (∀ i, Mat (n i))ˣ) (hg : ∀ i, unitProjection (fun i => Mat (n i)) i g ∈ N (n i))
    (w : PairSmooth n bs) :
    T (DerivativeSmoothVectors.representation 𝓘(ℝ, (∀ i, Mat (n i)))
      (productAction (fun i => Mat (n i)) (slotRepresentation n bs)) g w) =
    (∏ i, realWhittakerCharacter (oppositeScale a i) (unitProjection (fun i => Mat (n i)) i g)) * T w := by
  let A (i : Fin 2) := Mat (n i)
  let u (i : Fin 2) : N (n i) := ⟨unitProjection A i g, hg i⟩
  have hSplit : g = slot n 0 (u 0).val * slot n 1 (u 1).val := by
    apply Units.ext
    funext i
    change (u i).val.val = (unitProjection A i (slot n 0 (u 0).val * slot n 1 (u 1).val)).val
    rw [map_mul]
    have hi : i = 0 ∨ i = 1 := by fin_cases i <;> decide
    rcases hi with rfl | rfl
    · rw [unitProjection_slot_self, unitProjection_slot_of_ne n (by decide : (0 : Fin 2) ≠ 1), mul_one]
    · rw [unitProjection_slot_of_ne n (by decide : (1 : Fin 2) ≠ 0), unitProjection_slot_self, one_mul]
  rw [show ∏ i, realWhittakerCharacter (oppositeScale a i) (unitProjection A i g) =
    realWhittakerCharacter (oppositeScale a 0) (u 0).val *
      realWhittakerCharacter (oppositeScale a 1) (u 1).val from Fin.prod_univ_two _]
  nth_rw 1 [hSplit]
  rw [map_mul, Module.End.mul_apply, hT.2.1 0 (u 0), hT.2.1 1 (u 1), mul_assoc]

section Terminal

variable (r t : ℕ) (ds es : List RealBlock) (a : ℝˣ)

local notation "n" => pairRanks r t
local notation "bs" => pairLists ds es
local notation "A" => fun i => Mat (n i)
local notation "Alg" => (∀ i : Fin 2, A i)
local notation "E" => slotCarrier n bs
local notation "ρ" => slotRepresentation n bs
local notation "J" => PairSmooth n bs
local notation "F" => fun i => Automorphic.realStandardKFinite (n i + 1) (bs i)
local notation "Norm" => fun (f : ℂ → ℂ) => OrdinaryIntegralNormalization f (fun z => (L[ds, es].denominator z)⁻¹)

private local instance : ChartedSpace Alg Algˣ :=
  (Units.isOpenEmbedding_val (R := Alg)).singletonChartedSpace

set_option maxHeartbeats 1400000 in
private theorem terminalNormalizations_of_vanishing (hO : RealOrdinaryNormalizedContinuationStatement)
    (hrt : t ≤ r) (hd : realRank ds = r + 1) (he : realRank es = t + 1)
    (hm : ∀ i, t ≤ n i) (μ : ∀ k, RealQuotientMeasureData k) (s : ℂ)
    (B : ∀ i, F i →ₗ[ℂ] (G (n i) → ℂ)) (L : ∀ i, SlotSmooth n bs i →L[ℂ] ℂ) (T : J →L[ℂ] ℂ)
    (hB : ∀ i, IsRealWhittakerIntertwiner (n i) (bs i) (oppositeScale a i) (B i))
    (hL : ∀ i, IsWhittakerStandardEvaluation (bs i) (oppositeScale a i) (B i) (L i))
    (hT : IsPairedStandardForm n bs a L T) (hz : ¬ RealOrdinaryPairHasValueAt r t ds es a μ s) :
    ∀ v : J × Option (Rows t), IsPairedTerminalRow n t v.2 →
      Nonempty (Norm (ordinaryPaddedPairIntegral n E ρ t hm (μ t) T v)) ∧
      ∀ M : Norm (ordinaryPaddedPairIntegral n E ρ t hm (μ t) T v), M.value s = 0 := by
  have hR (i : Fin 2) : IsContinuousRepresentation (ρ i) := isContinuousRepresentation (bs i)
  have hEval := realPairedNormalizedEvaluation n E ρ hR a T t hm (μ t) hT.2.1 (hT.2.2 t hm)
    L[ds, es] (ArchimedeanRealPairFactor.realLFactor_ne_zero (realPairBlocks ds es))
  rcases lt_or_eq_of_le hrt with hlt | heq
  · let Z (v : J) := ordinaryPaddedPairIntegral n E ρ t hm (μ t) T (v, none)
    have hG := realPairedStandardUnequalGrowth r t ds es hO hlt hd he a (μ t) hm B L T hB hL hT
    have hN : HasEntireOrdinaryNormalizations Z L[ds, es] := fun v => (hG v).ordinaryNormalization
    have hCont := hEval.1 none (Or.inr ⟨0, hlt⟩) hN
    rintro ⟨v, _ | Φ⟩ hRow
    · refine ⟨hN v, fun M => ?_⟩
      by_contra hn
      exact hz (.of_unequal hlt (realPairedUnequalExactExtraction r t ds es a B L T hB hL hT hlt hm (μ t)
        hN hCont s ⟨v, M, hn⟩))
    · have heq' : r = t := hRow.1 0
      exact (hlt.ne heq'.symm).elim
  · subst t
    let nn := pairRanks r r
    let EE := slotCarrier nn bs
    let rr := slotRepresentation nn bs
    rintro ⟨v, _ | Φ⟩ hRow
    · obtain ⟨i, hi⟩ := hRow
      fin_cases i <;> exact (Nat.lt_irrefl _ hi).elim
    · let Z (v : PairSmooth nn bs) := ordinaryPaddedPairIntegral nn EE rr r hm (μ r) T (v, some Φ)
      have hG := realPairedStandardEqualGrowth ds es r hO hd he a (μ r) hm B L T hB hL hT Φ
      have hN : HasEntireOrdinaryNormalizations Z L[ds, es] := fun v => (hG v).ordinaryNormalization
      have hCont := hEval.1 (some Φ) (Or.inl rfl) hN
      refine ⟨hN v, fun M => ?_⟩
      by_contra hn
      exact hz (.of_equal (realPairedEqualExactExtraction r ds es a B L T hB hL hT hm (μ r) Φ
        hN hCont s ⟨v, M, hn⟩))

end Terminal

private theorem exists_leadingLift {r m p : ℕ} {ds d₁ d₂ : List RealBlock}
    (hr : r = p + 1 + m) (hd : ds = d₂ ++ d₁) (hm : m < r)
    (h₁ : realRank d₁ = m + 1) (h₂ : realRank d₂ = p + 1)
    (a : ℝˣ) (L : DerivativeSmoothVectors (matrixModel ℝ (r + 1)) (representation (n := r + 1) ds) →L[ℂ] ℂ)
    (hL : IsSmoothWhittakerEvaluation ds a L) (hLne : L ≠ 0) (W : realWhittakerModel m d₁ a) :
    ∀ φ : Test m p, ∃ v,
      HasLeadingBlockRestriction hm (fun g => L (DerivativeSmoothVectors.representation
        (matrixModel ℝ (r + 1)) (representation (n := r + 1) ds) g v)) (W : G m → ℂ) (compactRowProfile a φ) := by
  subst r ds
  obtain ⟨L₁, hL₁, hL₁ne, hPre⟩ := exists_realStandardWhittakerEvaluation m d₁ h₁ a
  obtain ⟨L₂, hL₂, hL₂ne, _⟩ := exists_realStandardWhittakerEvaluation p d₂ h₂ a
  obtain ⟨f, hf⟩ := hPre W
  obtain ⟨g, hLift⟩ := realCompactParabolicLeadingRestriction m p d₁ d₂ h₁ h₂ a L L₁ L₂ hL hL₁ hL₂ hLne hL₁ne hL₂ne
  intro φ
  refine ⟨smoothSectionVector h₁ h₂ f g φ, ?_⟩
  rw [← hf]
  exact hLift f φ

set_option maxHeartbeats 1500000 in
private theorem strictLeading_sorted (hO : RealOrdinaryNormalizedContinuationStatement)
    (r t m p : ℕ) (hrt : t ≤ r) (hmt : m < t) (ds es d₁ d₂ : List RealBlock)
    (hd : realRank ds = r + 1) (he : realRank es = t + 1)
    (h₁ : realRank d₁ = m + 1) (h₂ : realRank d₂ = p + 1)
    (i j : Fin 2) (hij : i ≠ j) (hi : pairRanks r t i = p + 1 + m) (hCut : pairLists ds es i = d₂ ++ d₁)
    (a : ℝˣ) (μ : ∀ k, RealQuotientMeasureData k) (s : ℂ)
    (hDen : L[d₂, pairLists ds es j].denominator s ≠ 0)
    (hLower : ∀ h : m < pairRanks r t j, HasNonzeroOrdinaryNormalizationAt
      (realOrdinaryUnequalTest h (pairLists ds es j) d₁ (oppositeScale a j) (μ m)) L[pairLists ds es j, d₁] s) :
    RealOrdinaryPairHasValueAt r t ds es a μ s := by
  by_contra hz
  let n := pairRanks r t
  let bs := pairLists ds es
  let E := slotCarrier n bs
  let ρ := slotRepresentation n bs
  let A (k : Fin 2) := Mat (n k)
  let : ChartedSpace (∀ k, A k) (∀ k, A k)ˣ :=
    (Units.isOpenEmbedding_val (R := ∀ k, A k)).singletonChartedSpace
  let J := PairSmooth n bs
  let χ := oppositeScale a i
  have hχ : oppositeScale a j = -χ := by
    fin_cases i <;> fin_cases j <;> simp_all [χ, oppositeScale]
  have hχ' : -oppositeScale a j = χ := by rw [hχ, neg_neg]
  have hRank (k : Fin 2) : realRank (bs k) = n k + 1 := by fin_cases k <;> assumption
  have hm (k : Fin 2) : t ≤ n k := by
    fin_cases k
    · exact hrt
    · exact le_rfl
  have hρ (k : Fin 2) : IsContinuousRepresentation (ρ k) := isContinuousRepresentation (bs k)
  obtain ⟨B, L, T, hData, hT⟩ := realPairedStandardModels n bs hRank a
  have hTerminal := terminalNormalizations_of_vanishing r t ds es a hO hrt hd he hm μ s B L T
    (fun k => (hData k).1) (fun k => (hData k).2.1) hT hz
  obtain ⟨σ, hConv⟩ := realPairedOrdinaryConvergence n E ρ hρ a T t hm (μ t) hT.2.1 (hT.2.2 t hm)
  let Z (v : J × Option (Rows t)) := ordinaryPaddedPairIntegral n E ρ t hm (μ t) T v
  let F (z : ℂ) := (L[ds, es].denominator z)⁻¹
  have hEntire : HasPairedTerminalNormalizations n E ρ t hm (μ t) T F := by
    intro v hv
    refine ⟨(hTerminal v hv).1, σ, (hConv v ?_).1⟩
    rcases v with ⟨v, _ | Φ⟩
    · exact Or.inr hv
    · exact Or.inl rfl
  let P := LinearMap.ker (LinearMap.proj s : (ℂ → ℂ) →ₗ[ℂ] ℂ)
  have hV (v : J × Option (Rows t)) (hv : IsPairedTerminalRow n t v.2) (M : OrdinaryIntegralNormalization (Z v) F) :
      M.value ∈ P := (hTerminal v hv).2 M
  let η : Measure Tail := Measure.haar
  have hRaise := realPairedRankTransfer n E ρ hρ t hm μ (realSelfDualMeasure a) η (NeZero.ne η) a T
    (fullCovariance n bs a L T hT) hT.2.2 m hmt
  obtain ⟨⟨V, W⟩, M, hM⟩ := hLower (hmt.trans_le (hm j))
  let W' : realWhittakerModel m d₁ χ := ⟨W, by simpa only [hχ'] using W.property⟩
  have hv : (V : G (n j) → ℂ) ∈ (B j).range := (hData j).2.2.2 ▸ V.property
  obtain ⟨v, hv⟩ := hv
  have hLift := exists_leadingLift hi hCut (hmt.trans_le (hm i)) h₁ h₂ χ (L i) (hData i).2.1.2 (hData i).2.2.1 W'
  have hL (u : N (n j)) (v : SlotSmooth n bs j) := (hData j).2.1.2 u v
  simp only [hχ] at hL
  obtain ⟨H, hH⟩ := realPairedStrictPrimalAt n E ρ i j hij χ L T hT.1 (hρ j) hL m t p hmt hm μ W'
    hLift hRaise F hEntire P hV (smoothOfCompact (bs j) v)
  have heq : (fun g => L j (DerivativeSmoothVectors.representation 𝓘(ℝ, A j) (ρ j) g (smoothOfCompact (bs j) v))) =
      (V : G (n j) → ℂ) := (funext ((hData j).2.1.1 v)).trans hv
  have hI : realUnequalIntegral (hmt.trans_le (hm j)) (μ m)
      (fun g => L j (DerivativeSmoothVectors.representation 𝓘(ℝ, A j) (ρ j) g (smoothOfCompact (bs j) v))) W' =
      realOrdinaryUnequalTest (hmt.trans_le (hm j)) (bs j) d₁ (oppositeScale a j) (μ m) (V, W) := by
    rw [heq]
    rfl
  let H' := H.congrIntegral hI
  let M' : OrdinaryIntegralNormalization
      (realOrdinaryUnequalTest (hmt.trans_le (hm j)) (bs j) d₁ (oppositeScale a j) (μ m) (V, W))
      (fun z => (L[d₁, bs j].denominator z)⁻¹) :=
    ⟨M.value, M.analytic, by simpa only [realPairLFactor_comm d₁ (bs j)] using M.eq_on_right⟩
  let Q := appendLeftNormalization d₁ d₂ (bs j) _ _ rfl M'
  have hPerm : L[d₂ ++ d₁, bs j] = L[d₁ ++ d₂, bs j] := realPairLFactor_perm (List.perm_append_comm) (List.Perm.refl _)
  have hFactor : L[ds, es] = L[d₁ ++ d₂, bs j] := by
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact (congrArg (fun x => L[x, es]) hCut).trans hPerm
    · exact (realPairLFactor_comm ds es).trans ((congrArg (fun x => L[x, ds]) hCut).trans hPerm)
    · exact (hij rfl).elim
  let Q' : OrdinaryIntegralNormalization _ F :=
    ⟨Q.value, Q.analytic, by simpa only [F, hFactor] using Q.eq_on_right⟩
  have hEq := Q'.value_eq_of_factor_ne_zero H' (realPairFactor_eventually_ne_zero ds es)
  have hzero : H'.value s = 0 := hH
  have hne : Q'.value s ≠ 0 := mul_ne_zero hDen hM
  exact hne ((congrFun hEq s).trans hzero)

/-- When the leading block rank is strictly below both ambient ranks, a nonzero
lower ordinary value lifts to a nonzero exact upper ordinary value wherever the
complementary pair denominator is nonzero. -/
def RealOrdinaryStrictLeadingDetectionStatement : Prop :=
  RealOrdinaryNormalizedContinuationStatement →
  ∀ (m p t : ℕ) (hmt : m < t) (d₁ d₂ es : List RealBlock),
    realRank d₁ = m + 1 → realRank d₂ = p + 1 → realRank es = t + 1 →
    ∀ (a : ℝˣ) (μ : ∀ k, RealQuotientMeasureData k) (s : ℂ),
      L[d₂, es].denominator s ≠ 0 →
      HasNonzeroOrdinaryNormalizationAt (realOrdinaryUnequalTest hmt es d₁ (-a) (μ m)) L[es, d₁] s →
      RealOrdinaryPairHasValueAt (p + 1 + m) t (d₂ ++ d₁) es a μ s

set_option maxHeartbeats 1400000 in
theorem realOrdinaryStrictLeadingDetection : RealOrdinaryStrictLeadingDetectionStatement := by
  intro hO m p t hmt d₁ d₂ es h₁ h₂ he a μ s hDen hLower
  let r := p + 1 + m
  have hd : realRank (d₂ ++ d₁) = r + 1 := by
    rw [realRank_append, h₂, h₁]
    dsimp [r]
    omega
  rcases le_total t r with htr | hrt
  · exact strictLeading_sorted hO r t m p htr hmt (d₂ ++ d₁) es d₁ d₂ hd he h₁ h₂ 0 1
      (by decide) rfl rfl a μ s hDen (fun _ => hLower)
  · have h := strictLeading_sorted hO t r m p hrt (show m < r by dsimp [r]; omega) es (d₂ ++ d₁) d₁ d₂ he hd h₁ h₂ 1 0
      (by decide) rfl rfl (-a) μ s hDen (fun _ => hLower)
    have hh := h.swap
    rw [show -(-a) = a from neg_neg a] at hh
    exact hh

/-- A nonzero ordinary value lifts from the leading block across any comparison rank,
provided the complementary denominator is nonzero. -/
theorem RealOrdinaryPairHasValueAt.leadingLift (hO : RealOrdinaryNormalizedContinuationStatement)
    {m p t : ℕ} {d₁ d₂ es : List RealBlock} (h₁ : realRank d₁ = m + 1)
    (h₂ : realRank d₂ = p + 1) (he : realRank es = t + 1)
    {a : ℝˣ} {μ : ∀ k, RealQuotientMeasureData k} {s : ℂ}
    (hDen : L[d₂, es].denominator s ≠ 0) (hLower : RealOrdinaryPairHasValueAt m t d₁ es a μ s) :
    RealOrdinaryPairHasValueAt (p + 1 + m) t (d₂ ++ d₁) es a μ s := by
  rcases le_or_gt t m with htm | hmt
  · refine .of_unequal (show t < p + 1 + m by omega)
      (realOrdinaryLeadingDetection hO m p t htm d₁ d₂ es h₁ h₂ he a (μ t) s hDen hLower.1 ?_)
    intro h
    subst t
    exact hLower.2.2 rfl
  · exact realOrdinaryStrictLeadingDetection hO m p t hmt d₁ d₂ es h₁ h₂ he a μ s hDen (hLower.2.1 hmt)

end Langlands.Global.RankinSelbergGlobal
