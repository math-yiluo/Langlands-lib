import Langlands.Representation.Classification.SegmentSocleDerivativesProof
import Langlands.Representation.Classification.SegmentProductOrderedAssembly
import Langlands.Representation.Derivative.HighestProduct

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Classification

open GeneralLinear PadicField.TopologicalData Derivative
open SegmentProductOrderedAssembly

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

private theorem datum_cons {q : ℕ}
    (segments : Fin (q + 1) → Segment.{uV, uF} T)
    (blocks : letI := T.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (segments i).degree F.Carrier)) :
    letI := T.topology
    cons (segments 0) (blocks 0)
      (⟨q, Fin.tail segments, rfl, fun i => blocks i.succ⟩ :
        SegmentProductDatum.{uV, uF} T (∑ i : Fin q, (segments i.succ).degree)) =
    (⟨q + 1, segments, Fin.sum_univ_succ _, blocks⟩ :
      SegmentProductDatum.{uV, uF} T ((segments 0).degree +
        ∑ i : Fin q, (segments i.succ).degree)) := by
  let _ := T.topology
  cases segments using Fin.consCases with
  | cons Δ segments =>
    cases blocks using Fin.consCases with
    | cons A blocks => rfl

private theorem rank_le_degree (Δ : Segment.{uV, uF} T) : Δ.rank ≤ Δ.degree := by
  simpa using Nat.mul_le_mul_right Δ.rank Δ.length_pos

private theorem rank_sum_le {n : ℕ} (d : SegmentProductDatum.{uV, uF} T n) :
    (∑ i, (d.segments i).rank) ≤ n := by
  calc
    (∑ i, (d.segments i).rank) ≤ ∑ i, (d.segments i).degree :=
      Finset.sum_le_sum (fun i _ => rank_le_degree T (d.segments i))
    _ = n := d.degree_sum

private theorem castRank_eq {a b : ℕ} (h : a = b)
    (A : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier)) :
    letI := T.topology
    T.castRank h A = (generalLinearRankCast T h).obj A := by
  subst b
  rfl

private def binaryRankIso {a a' b b' c : ℕ}
    (ha : a = a') (hb : b = b') (hc : a + b = c) (hc' : a' + b' = c)
    (A : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier)) :
    letI := T.topology
    (generalLinearRankCast T hc).obj
        ((T.binaryNormalizedProductFunctor a b).obj (A, B)) ≅
      (generalLinearRankCast T hc').obj
        ((T.binaryNormalizedProductFunctor a' b').obj
          ((generalLinearRankCast T ha).obj A, (generalLinearRankCast T hb).obj B)) := by
  let _ := T.topology
  subst a'
  subst b'
  subst c
  exact Iso.refl _

private theorem omitLine {a b c : ℕ}
    (ha : a = 0) (hc : a + b = c) (hb : b = c)
    (A : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier))
    (hA : letI := T.topology; Module.finrank ℂ A = 1) :
    letI := T.topology
    Nonempty ((generalLinearRankCast T hc).obj
        ((T.binaryNormalizedProductFunctor a b).obj (A, B)) ≅
      (generalLinearRankCast T hb).obj B) := by
  let _ := T.topology
  subst a
  cases hc
  exact nonempty_iso_omit_left_line T A B hA

private def truncateSegment (Δ : Segment.{uV, uF} T) : Option (Segment.{uV, uF} T) :=
  if h : 2 ≤ Δ.length then some ⟨Δ.base, Δ.length - 1, by omega⟩ else none

private def ProductCalculation
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    {n : ℕ} (d : SegmentProductDatum.{uV, uF} T n) (k : ℕ) (hk : k ≤ n) : Prop :=
  letI := T.topology
  (∀ (j : ℕ) (hj : j ≤ n), k < j →
    Subsingleton ((generalLinearDerivative T ψ n j hj).obj d.induced)) ∧
  ∃ d' : SegmentProductDatum.{uV, uF} T (n - k),
    List.ofFn d'.segments = (List.ofFn d.segments).filterMap (truncateSegment T) ∧
    d'.HasSegmentSocles ∧
    Nonempty ((generalLinearDerivative T ψ n k hk).obj d.induced ≅ d'.induced)

private theorem cons_calculation
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    {n s : ℕ} (Δ : Segment.{uV, uF} T)
    (A : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (d : SegmentProductDatum.{uV, uF} T n)
    (hA : T.IsSegmentSocle Δ A) (hs : s ≤ n)
    (hcalc : ProductCalculation T ψ d s hs)
    (hrs : Δ.rank + s ≤ Δ.degree + n) :
    ProductCalculation T ψ (cons Δ A d) (Δ.rank + s) hrs := by
  let _ := T.topology
  rcases hcalc with ⟨hB, d', hlist, hd', ⟨eB⟩⟩
  have hr := rank_le_degree T Δ
  have hseg := segmentSocleDerivatives F T ψ Δ A hA
  have hbound : ∀ j (hj : j ≤ Δ.degree), Δ.rank < j →
      Subsingleton ((generalLinearDerivative T ψ Δ.degree j hj).obj A) :=
    fun j hj hlt => hseg.1 j hj (by omega) (by omega)
  obtain ⟨eP⟩ := nonempty_cons_iso_binary Δ A d
  refine ⟨?_, ?_⟩
  · intro j hj hlt
    let _ := HighestProduct.subsingleton_above T ψ A d.induced Δ.rank s
      hbound hB j hj hlt
    exact (SmoothRep.equivOfIso
      ((generalLinearDerivative T ψ (Δ.degree + n) j hj).mapIso eP)).toEquiv.injective.subsingleton
  · let a := Δ.degree - Δ.rank
    let b := n - s
    let c := (Δ.degree + n) - (Δ.rank + s)
    have hc : a + b = c := by dsimp [a, b, c]; omega
    let AD := (generalLinearDerivative T ψ Δ.degree Δ.rank hr).obj A
    let E : (generalLinearDerivative T ψ (Δ.degree + n) (Δ.rank + s) hrs).obj
        (cons Δ A d).induced ≅
      (generalLinearRankCast T hc).obj
        ((T.binaryNormalizedProductFunctor a b).obj (AD, d'.induced)) :=
      (generalLinearDerivative T ψ (Δ.degree + n) (Δ.rank + s) hrs).mapIso eP ≪≫
        HighestProduct.highestProductIso T ψ A d.induced Δ.rank s hr hs hbound hB hrs ≪≫
        (generalLinearRankCast T hc).mapIso
          ((T.binaryNormalizedProductFunctor a b).mapIso (Iso.prod (Iso.refl AD) eB))
    by_cases h₂ : 2 ≤ Δ.length
    · let Δ' : Segment.{uV, uF} T := ⟨Δ.base, Δ.length - 1, by omega⟩
      have ha : a = Δ'.degree := by
        simpa only [a, Segment.degree, Δ', Nat.one_mul] using
          (Nat.sub_mul Δ.length 1 Δ.rank).symm
      let A' := (generalLinearRankCast T ha).obj AD
      have hA' : T.IsSegmentSocle Δ' A' := by
        have h := hseg.2.2 hr h₂ ha
        change T.IsSegmentSocle Δ' (T.castRank ha AD) at h
        rw [castRank_eq T] at h
        exact h
      have hout : Δ'.degree + b = c := by omega
      let dout := rankCast hout (cons Δ' A' d')
      refine ⟨dout, ?_, rankCast_hasSegmentSocles _ _
        (cons_hasSegmentSocles Δ' A' d' hA' hd'), ?_⟩
      · change List.ofFn (cons Δ' A' d').segments =
          (List.ofFn (cons Δ A d).segments).filterMap (truncateSegment T)
        rw [cons_segments, cons_segments, List.filterMap_cons, show truncateSegment T Δ = some Δ' by
          simp only [truncateSegment, dite_eq_left h₂]
          rfl, hlist]
      · obtain ⟨econs⟩ := nonempty_cons_iso_binary Δ' A' d'
        exact ⟨E ≪≫ binaryRankIso T ha rfl hc hout AD d'.induced ≪≫
          (generalLinearRankCast T hout).mapIso econs.symm ≪≫
          (eqToIso (rankCast_induced hout (cons Δ' A' d'))).symm⟩
    · have h₁ : Δ.length = 1 := by have := Δ.length_pos; omega
      have ha : a = 0 := by simp only [a, Segment.degree, h₁, Nat.one_mul, Nat.sub_self]
      have hout : b = c := by omega
      let dout := rankCast hout d'
      refine ⟨dout, ?_, rankCast_hasSegmentSocles _ _ hd', ?_⟩
      · change List.ofFn d'.segments =
          (List.ofFn (cons Δ A d).segments).filterMap (truncateSegment T)
        rw [cons_segments, List.filterMap_cons, show truncateSegment T Δ = none by
          simp only [truncateSegment, dite_eq_right h₂]]
        exact hlist
      · obtain ⟨eomit⟩ := omitLine T ha hc hout AD d'.induced (hseg.2.1 hr h₁)
        exact ⟨E ≪≫ eomit ≪≫ (eqToIso (rankCast_induced hout d')).symm⟩

private theorem product_calculation
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (q : ℕ) :
    ∀ (n : ℕ) (d : SegmentProductDatum.{uV, uF} T n),
      d.HasSegmentSocles → d.length = q →
      ∀ (k : ℕ) (hk : k ≤ n), k = ∑ i, (d.segments i).rank →
        ProductCalculation T ψ d k hk := by
  let _ := T.topology
  induction q with
  | zero =>
    intro n d hd hlen k hk hsumrank
    rcases d with ⟨r, segments, hsum, blocks⟩
    dsimp at hlen
    subst r
    have hn : n = 0 := by simpa using hsum.symm
    subst n
    have hk0 : k = 0 := by simpa using hsumrank
    subst k
    refine ⟨?_, ?_⟩
    · intro j hj hlt
      omega
    · refine ⟨⟨0, segments, by simp, blocks⟩, ?_, hd, ⟨Iso.refl _⟩⟩
      rfl
  | succ q ih =>
    intro n d hd hlen k hk hsumrank
    rcases d with ⟨r, segments, hsum, blocks⟩
    dsimp at hlen
    subst r
    rw [Fin.sum_univ_succ] at hsum
    cases hsum
    let tail : SegmentProductDatum.{uV, uF} T (∑ i : Fin q, (segments i.succ).degree) :=
      ⟨q, Fin.tail segments, rfl, fun i => blocks i.succ⟩
    have htail : tail.HasSegmentSocles := fun i => hd i.succ
    have hs := rank_sum_le T tail
    have hcalc := ih _ tail htail rfl _ hs rfl
    have hsplit : k = (segments 0).rank + ∑ i : Fin q, (segments i.succ).rank := by
      simpa only [Fin.sum_univ_succ] using hsumrank
    clear hsumrank
    subst k
    have C := cons_calculation T ψ (segments 0) (blocks 0) tail (hd 0) hs hcalc hk
    rwa [datum_cons T segments blocks] at C

private theorem finrank_datum_zero {n : ℕ} (hn : n = 0)
    (d : SegmentProductDatum.{uV, uF} T n) :
    letI := T.topology; Module.finrank ℂ d.induced = 1 := by
  subst n
  exact finrank_zeroDatum d

/-- The actual highest derivative of every ordered product of segment socles. -/
theorem segmentSocleProductHighestDerivative
    (F : PadicField.{uF} p) (T : F.TopologicalData) :
    SegmentSocleProductHighestDerivative.{uF, uV} F T := by
  let _ := T.topology
  intro ψ n d hd k hk hsumrank
  obtain ⟨hvanish, d', hlist, hd', ⟨e⟩⟩ :=
    product_calculation T ψ d.length n d hd rfl k hk hsumrank
  refine ⟨hvanish, ⟨d', hlist, hd', ⟨e⟩⟩, ?_⟩
  intro hall
  have hnk : n = k := by
    calc
      n = ∑ i, (d.segments i).degree := d.degree_sum.symm
      _ = ∑ i, (d.segments i).rank := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [Segment.degree, hall i, Nat.one_mul]
      _ = k := hsumrank.symm
  exact (SmoothRep.equivOfIso e).toLinearEquiv.finrank_eq.trans
    (finrank_datum_zero T (by omega : n - k = 0) d')

end Langlands.Classification
