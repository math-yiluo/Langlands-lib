import Langlands.Representation.Classification.TadicExhaustionLemmasStatement
import Langlands.Representation.Classification.TadicRectangleCombinatorics
import Langlands.Representation.Classification.SegmentHeadProductTerminalSupport
import Langlands.Representation.Classification.SegmentSocleDerivativeConstituentSupport
import Langlands.Representation.Classification.SegmentHeadSupportStep
import Langlands.Representation.Derivative.GeneralLinearHighestDerivativeOrder
import Langlands.Representation.Derivative.GeneralLinearDerivativeFiniteLengthProof
import Langlands.Representation.Derivative.ProductDerivativeSupportAggregation
import Langlands.Representation.Classification.TadicSpehHeads
import Langlands.HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsProof

/-!
# Tadić's Lemma 6.3: `L(a(n,d)^ρ) ≇ ⟨a(n,d)^ρ⟩` for `0 < n < d`

A positive-order derivative constituent of a Zelevinsky socle of `a(n,d)^ρ` has
the cuspidal content of `a(n,d)^ρ` with some segment ends removed as support; one
of a Langlands head has, segment by segment, terminal truncations, with at least
one segment beginning removed. For `n < d` every segment beginning has a negative
exponent and every segment end a positive one, so the two supports contain
different numbers of members with negative exponent. Uniqueness of supercuspidal
support then excludes an isomorphism.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Classification

open GeneralLinear PadicField.TopologicalData Derivative

universe uF uV

namespace TadicRectangleHeadSocle

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

section Counting

/-- Counting members satisfying a predicate commutes with finite sums. -/
theorem countP_finset_sum {ι α : Type*} (P : α → Prop) [DecidablePred P] (s : Finset ι)
    (f : ι → Multiset α) : (∑ i ∈ s, f i).countP P = ∑ i ∈ s, (f i).countP P :=
  map_sum (Multiset.countPAddMonoidHom P) f s

/-- Among `β, νβ, …, ν^(l-1) β`, exactly `min l L` satisfy a predicate that holds
for `ν^j β` exactly when `j < L`. -/
theorem countP_ofFn_twist (β : T.CuspidalDatum.{uV, uF}) (P : T.CuspidalDatum.{uV, uF} → Prop)
    [DecidablePred P] (L : ℕ) :
    ∀ l : ℕ, (∀ j < l, P (β.twist ((j : ℕ) : ℝ)) ↔ j < L) →
      (List.ofFn fun i : Fin l => β.twist (((i : ℕ) : ℕ) : ℝ)).countP
        (fun x => decide (P x)) = min l L
  | 0, _ => by simp
  | l + 1, hP => by
    rw [List.ofFn_succ', List.concat_eq_append, List.countP_append]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [countP_ofFn_twist β P L l (fun j hj => hP j (by omega))]
    by_cases h : l < L
    · have hl := (hP l (by omega)).mpr h
      simp [hl]
      omega
    · have hl := mt (hP l (by omega)).mp h
      simp [hl]
      omega

/-- The number of members of a segment satisfying a predicate that holds exactly
for the first `L` members. -/
theorem countP_cuspidalContent (Δ : T.Segment.{uV, uF}) (P : T.CuspidalDatum.{uV, uF} → Prop)
    [DecidablePred P] (L : ℕ) (hL : L ≤ Δ.length)
    (hP : ∀ j < Δ.length, P (Δ.member j) ↔ j < L) :
    Δ.cuspidalContent.countP P = L := by
  have h := countP_ofFn_twist Δ.base P L Δ.length hP
  rw [min_eq_right hL] at h
  rw [Segment.cuspidalContent, Multiset.coe_countP]
  exact h

/-- Removing the end of a segment does not change the number of members
satisfying a predicate that fails at the end. -/
theorem countP_residualContent (Δ : T.Segment.{uV, uF}) (P : T.CuspidalDatum.{uV, uF} → Prop)
    [DecidablePred P] (L : ℕ) (hL : L < Δ.length)
    (hP : ∀ j < Δ.length, P (Δ.member j) ↔ j < L) (b : Bool) :
    (SegmentSocleDerivativeConstituentSupport.residualContent T Δ b).countP P = L := by
  cases b with
  | false =>
    simp only [SegmentSocleDerivativeConstituentSupport.residualContent, Bool.false_eq_true,
      ↓reduceIte]
    exact countP_cuspidalContent Δ P L hL.le hP
  | true =>
    simp only [SegmentSocleDerivativeConstituentSupport.residualContent, ↓reduceIte]
    split_ifs with h2
    · have h := countP_ofFn_twist Δ.base P L (Δ.length - 1)
        (fun j hj => hP j (by omega))
      rw [min_eq_right (by omega)] at h
      rw [Segment.cuspidalContent, Multiset.coe_countP]
      exact h
    · have : L = 0 := by omega
      simp [this]

/-- A multiset whose underlying set is a terminal window of `Δ` and whose size is
at most `Δ.length - c` has at most `L - c` members satisfying a predicate that holds
exactly for the first `L` members of `Δ`. -/
theorem countP_add_le_of_window (Δ : T.Segment.{uV, uF}) (P : T.CuspidalDatum.{uV, uF} → Prop)
    [DecidablePred P] (L : ℕ) (hL1 : 1 ≤ L) (hLd : L ≤ Δ.length)
    (hP : ∀ j < Δ.length, P (Δ.member j) ↔ j < L)
    (s : Multiset (T.CuspidalDatum.{uV, uF})) (a : ℕ)
    (hs : {x | x ∈ s} = SegmentHeadSupport.window Δ.base a Δ.length)
    (c : ℕ) (hc : c ≤ 1) (hcard : Multiset.card s + c ≤ Δ.length) :
    s.countP P + c ≤ L := by
  by_cases haL : L ≤ a
  · have h0 : s.countP P = 0 := by
      rw [Multiset.countP_eq_zero]
      intro x hx hPx
      obtain ⟨j, haj, hj, rfl⟩ := (Set.ext_iff.mp hs x).mp hx
      have := (hP j hj).mp hPx
      omega
    omega
  · push Not at haL
    let H : Multiset (T.CuspidalDatum.{uV, uF}) :=
      (List.ofFn fun i : Fin (Δ.length - L) => Δ.member (L + (i : ℕ)) : Multiset _)
    have hHnd : H.Nodup := by
      apply Multiset.coe_nodup.mpr
      apply List.nodup_ofFn.mpr
      intro i i' h
      have := SegmentHeadSupport.member_inj Δ h
      exact Fin.ext (by omega)
    have hHle : H ≤ s.filter (fun x => ¬ P x) := by
      apply (Multiset.le_iff_subset hHnd).mpr
      intro x hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (Multiset.mem_coe.mp hx)
      rw [Multiset.mem_filter]
      refine ⟨(Set.ext_iff.mp hs _).mpr ⟨L + (i : ℕ), by omega, by omega, rfl⟩, ?_⟩
      intro hPx
      have := (hP (L + (i : ℕ)) (by omega)).mp hPx
      omega
    have hcardH : Multiset.card H = Δ.length - L := by
      simp [H]
    have h1 := Multiset.card_le_card hHle
    have h2 := Multiset.card_eq_countP_add_countP P s
    rw [← Multiset.countP_eq_card_filter] at h1
    omega

end Counting

section Factors

/-- An irreducible constituent of an order-`k` derivative of a segment head has a
support with at most `L` members satisfying a predicate that holds exactly for the
first `L` members of the segment, and at most `L - 1` when `k > 0`. -/
theorem head_factor_support
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (Δ : T.Segment.{uV, uF})
    (H : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (hH : T.IsSegmentHead Δ H) (k : ℕ) (hk : k ≤ Δ.degree)
    (E : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (Δ.degree - k) F.Carrier))
    (hE : letI := T.topology; E.IsIrreducible)
    (hEH : letI := T.topology
      SmoothRep.IsSubquotient E ((generalLinearDerivative T ψ Δ.degree k hk).obj H))
    (P : T.CuspidalDatum.{uV, uF} → Prop) [DecidablePred P] (L : ℕ) (hL1 : 1 ≤ L)
    (hLd : L ≤ Δ.length) (hP : ∀ j < Δ.length, P (Δ.member j) ↔ j < L) :
    ∃ s, T.IsSupercuspidalSupport E s ∧ s.countP P + (if 0 < k then 1 else 0) ≤ L := by
  let := T.topology
  obtain ⟨s, A, hs, hA, hset⟩ :=
    segmentHeadDerivativeSupportTruncation F T ψ Δ H hH k hk E hE hEH
  obtain ⟨a, -, hwin⟩ := (SegmentHeadSupport.exists_terminal_iff Δ {x | x ∈ s}).mp
    ⟨A, hA, hset⟩
  refine ⟨s, hs, countP_add_le_of_window Δ P L hL1 hLd hP s a hwin _
    (by split_ifs <;> omega) ?_⟩
  obtain ⟨m, ρ', hρ', hrank, -⟩ := hs
  have hrk : ∀ i, (ρ' i).rank = Δ.rank := by
    intro i
    have hmem : ρ' i ∈ s := by
      rw [← hρ']
      exact Multiset.mem_coe.mpr (List.mem_ofFn.mpr ⟨i, rfl⟩)
    obtain ⟨j, -, -, hj⟩ := (Set.ext_iff.mp hwin _).mp hmem
    rw [← hj]
    rfl
  have hcard : Multiset.card s = m := by
    rw [← hρ']
    simp
  have hsum : ∑ i, (ρ' i).rank = m * Δ.rank := by
    simp [hrk]
  rw [hsum] at hrank
  have hr := Δ.rank_pos
  have hdeg : Δ.degree = Δ.length * Δ.rank := rfl
  rw [hcard]
  split_ifs with hk0
  · have hlt : m * Δ.rank < Δ.length * Δ.rank := by omega
    have := Nat.lt_of_mul_lt_mul_right hlt
    omega
  · have hle : m * Δ.rank ≤ Δ.length * Δ.rank := by omega
    have := Nat.le_of_mul_le_mul_right hle hr
    omega

/-- An irreducible constituent of a derivative of a segment socle has a support
with exactly `L` members satisfying a predicate that holds exactly for the first
`L` members of the segment, when the segment end fails it. -/
theorem socle_factor_support
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (Δ : T.Segment.{uV, uF})
    (S : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (hS : T.IsSegmentSocle Δ S) (k : ℕ) (hk : k ≤ Δ.degree)
    (E : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (Δ.degree - k) F.Carrier))
    (hE : letI := T.topology; E.IsIrreducible)
    (hES : letI := T.topology
      SmoothRep.IsSubquotient E ((generalLinearDerivative T ψ Δ.degree k hk).obj S))
    (P : T.CuspidalDatum.{uV, uF} → Prop) [DecidablePred P] (L : ℕ)
    (hL : L < Δ.length) (hP : ∀ j < Δ.length, P (Δ.member j) ↔ j < L) :
    ∃ s, T.IsSupercuspidalSupport E s ∧ s.countP P = L := by
  obtain ⟨b, -, hs⟩ :=
    SegmentSocleDerivativeConstituentSupport.segment_support T ψ Δ S hS k hk E hE hES
  exact ⟨_, hs, countP_residualContent Δ P L hL hP b⟩

end Factors

section Rectangle

/-- In each segment of `a(n,d)^ρ` with `n < d`, the members `ν^y ρ` with `y < 0` are
exactly the first `L` members, for some `1 ≤ L < d`. -/
theorem exists_negative_prefix {ρ : T.CuspidalDatum.{uV, uF}} {n d : ℕ} {hd : 0 < d}
    (hnd : n < d) {Δ : T.Segment.{uV, uF}} (hΔ : Δ ∈ tadicMultisegment ρ n d hd) :
    ∃ L, 1 ≤ L ∧ L < Δ.length ∧
      ∀ j < Δ.length, (∃ y : ℝ, y < 0 ∧ Δ.member j = ρ.twist y) ↔ j < L := by
  obtain ⟨j0, hj0, rfl⟩ := mem_tadicMultisegment.mp hΔ
  set x : ℝ := (j0 : ℝ) - ((n : ℝ) - 1) / 2 with hx
  have hneg : ∀ j : ℕ,
      (∃ y : ℝ, y < 0 ∧ (tadicCenteredSegment ρ d hd x).member j = ρ.twist y) ↔
        (j : ℝ) < ((d : ℝ) - 1) / 2 - x := by
    intro j
    have hmem : (tadicCenteredSegment ρ d hd x).member j =
        ρ.twist ((j : ℝ) + (x - ((d : ℝ) - 1) / 2)) := by
      simp only [Segment.member, tadicCenteredSegment, CuspidalDatum.twist_twist]
    rw [hmem]
    constructor
    · rintro ⟨y, hy, he⟩
      have := cuspidalDatum_twist_injective ρ he
      linarith
    · intro h
      exact ⟨_, by linarith, rfl⟩
  have hj0' : (j0 : ℝ) + 1 ≤ n := by exact_mod_cast hj0
  have hnd' : (n : ℝ) + 1 ≤ d := by exact_mod_cast hnd
  have hj0nn : (0 : ℝ) ≤ j0 := Nat.cast_nonneg _
  refine ⟨⌈((d : ℝ) - 1) / 2 - x⌉₊, ?_, ?_, fun j _ => (hneg j).trans Nat.lt_ceil.symm⟩
  · rw [Nat.one_le_iff_ne_zero, ne_eq, Nat.ceil_eq_zero, not_le]
    linarith
  · show _ < d
    have hle : ⌈((d : ℝ) - 1) / 2 - x⌉₊ ≤ d - 1 := by
      rw [Nat.ceil_le, Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
      linarith
    omega

/-- Summing a function over the segments of a datum is summing it over its
multisegment. -/
theorem sum_segments_eq {N : ℕ} (D : T.SegmentProductDatum.{uV, uF} N)
    (f : T.Segment.{uV, uF} → ℕ) :
    ∑ i, f (D.segments i) = (D.multisegment.map f).sum := by
  simp [SegmentProductDatum.multisegment, List.sum_ofFn]

variable (F T) in
/-- Tadić 1986, Lemma 6.3: for `0 < n < d`, a Langlands head of `a(n,d)^ρ` is not
isomorphic to a Zelevinsky socle of `a(n,d)^ρ`. -/
theorem tadicRectangleHeadSocleDistinct : TadicRectangleHeadSocleDistinct.{uF, uV} F T := by
  let := T.topology
  classical
  intro ρ n d hd hn hnd N π π' hπ hπ' ⟨e⟩
  obtain ⟨ψ⟩ := HarmonicAnalysis.padicUnitaryAdditiveCharacterExists F T
  let P : T.CuspidalDatum.{max uF uV, uF} → Prop := fun c => ∃ y : ℝ, y < 0 ∧ c = ρ.twist y
  let Lf : T.Segment.{max uF uV, uF} → ℕ := fun Δ => Δ.cuspidalContent.countP P
  have hNpos : 0 < N := by
    rw [tadicMultisegment_rank_eq_of_isZelevinskySocle hπ']
    exact Nat.mul_pos hn (Nat.mul_pos hd ρ.rank_pos)
  obtain ⟨dH, hdH, -, hhH, hπH⟩ := hπ
  obtain ⟨dS, hdS, -, hsS, hπS⟩ := hπ'
  have hπirr : π.IsIrreducible := hπH.1
  -- An irreducible subrepresentation `D` of a highest derivative of `π`.
  let w := chooseGeneralLinearHighestDerivativeOrder T ψ hNpos π
    (SegmentHeadSupport.nontrivial_of_isIrreducible hπirr)
  have hfin := generalLinearDerivativeFiniteLength F T ψ N w.order w.le_rank π
    (SmoothRep.hasFiniteLength_of_isIrreducible hπirr)
  have := w.nonzero
  obtain ⟨D, hD, j, hj⟩ := SegmentHeadSupport.exists_irreducible_subrepresentation hfin
  have hDπ : SmoothRep.IsSubquotient D
      ((generalLinearDerivative T ψ N w.order w.le_rank).obj π) :=
    SmoothRep.IsSubrepresentation.isSubquotient ⟨j, hj⟩
  have hDπ' : SmoothRep.IsSubquotient D
      ((generalLinearDerivative T ψ N w.order w.le_rank).obj π') :=
    hDπ.of_iso_right ((generalLinearDerivative T ψ N w.order w.le_rank).mapIso e)
  -- `π` is a quotient of the head product and `π'` a subrepresentation of the socle
  -- product.
  obtain ⟨-, q, hq, -⟩ := hπH
  have hQH : SmoothRep.IsSubquotient π
      ((T.normalizedProductInductionFunctor dH.shape).obj dH.blocks) :=
    SmoothRep.IsQuotient.isSubquotient ⟨SmoothRep.ofHom q, hq⟩
  obtain ⟨-, i, hi, -⟩ := hπS
  have hQS : SmoothRep.IsSubquotient π'
      ((T.normalizedProductInductionFunctor dS.shape).obj dS.blocks) :=
    SmoothRep.IsSubrepresentation.isSubquotient ⟨SmoothRep.ofHom i, hi⟩
  have hmemH : ∀ i, dH.segments i ∈ tadicMultisegment ρ n d hd := fun i =>
    hdH ▸ (by simp [SegmentProductDatum.multisegment] : dH.segments i ∈ dH.multisegment)
  have hmemS : ∀ i, dS.segments i ∈ tadicMultisegment ρ n d hd := fun i =>
    hdS ▸ (by simp [SegmentProductDatum.multisegment] : dS.segments i ∈ dS.multisegment)
  -- Head side: each factor loses at least one member with negative exponent when
  -- its derivative order is positive.
  let PH : Fin dH.shape.length → ℕ → Multiset (T.CuspidalDatum.{max uF uV, uF}) → Prop :=
    fun i k s => s.countP P + (if 0 < k then 1 else 0) ≤ Lf (dH.segments i)
  have hFinH : ∀ i k (hk : k ≤ dH.shape.size i),
      ((generalLinearDerivative T ψ (dH.shape.size i) k hk).obj (dH.blocks i)).HasFiniteLength :=
    fun i k hk => generalLinearDerivativeFiniteLength F T ψ _ k hk _
      (SmoothRep.hasFiniteLength_of_isIrreducible (hhH i).choose_spec.2.1)
  have hSuppH : ∀ i k (hk : k ≤ dH.shape.size i)
      (E : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (dH.shape.size i - k) F.Carrier)),
      E.IsIrreducible →
      SmoothRep.IsSubquotient E ((generalLinearDerivative T ψ (dH.shape.size i) k hk).obj
        (dH.blocks i)) →
      ∃ s, PH i k s ∧ T.IsSupercuspidalSupport E s := by
    intro i k hk E hE hEH
    obtain ⟨L, hL1, hLd, hP⟩ := exists_negative_prefix hnd (hmemH i)
    obtain ⟨s, hs, hc⟩ := head_factor_support ψ (dH.segments i) (dH.blocks i) (hhH i) k hk
      E hE hEH P L hL1 hLd.le hP
    refine ⟨s, ?_, hs⟩
    show _ ≤ (dH.segments i).cuspidalContent.countP P
    rw [countP_cuspidalContent (dH.segments i) P L hLd.le hP]
    exact hc
  -- Socle side: each factor keeps all members with negative exponent.
  let PS : Fin dS.shape.length → ℕ → Multiset (T.CuspidalDatum.{max uF uV, uF}) → Prop :=
    fun i _ s => s.countP P = Lf (dS.segments i)
  have hFinS : ∀ i k (hk : k ≤ dS.shape.size i),
      ((generalLinearDerivative T ψ (dS.shape.size i) k hk).obj (dS.blocks i)).HasFiniteLength :=
    fun i k hk => generalLinearDerivativeFiniteLength F T ψ _ k hk _
      (SmoothRep.hasFiniteLength_of_isIrreducible (hsS i).choose_spec.2.1)
  have hSuppS : ∀ i k (hk : k ≤ dS.shape.size i)
      (E : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (dS.shape.size i - k) F.Carrier)),
      E.IsIrreducible →
      SmoothRep.IsSubquotient E ((generalLinearDerivative T ψ (dS.shape.size i) k hk).obj
        (dS.blocks i)) →
      ∃ s, PS i k s ∧ T.IsSupercuspidalSupport E s := by
    intro i k hk E hE hES
    obtain ⟨L, -, hLd, hP⟩ := exists_negative_prefix hnd (hmemS i)
    obtain ⟨s, hs, hc⟩ := socle_factor_support ψ (dS.segments i) (dS.blocks i) (hsS i) k hk
      E hE hES P L hLd hP
    refine ⟨s, ?_, hs⟩
    show _ = (dS.segments i).cuspidalContent.countP P
    rw [countP_cuspidalContent (dS.segments i) P L hLd.le hP]
    exact hc
  let sdH := ProductDerivativeSupport.supportDataOfSubquotient T ψ hNpos w.le_rank dH.shape
    dH.blocks π hQH D PH hFinH hSuppH hD hDπ
  let sdS := ProductDerivativeSupport.supportDataOfSubquotient T ψ hNpos w.le_rank dS.shape
    dS.blocks π' hQS D PS hFinS hSuppS hD hDπ'
  -- Uniqueness of supercuspidal support.
  have hsupp : ∑ i, (sdH.factors i).cuspidalSupport = ∑ i, (sdS.factors i).cuspidalSupport := by
    by_cases hr : 0 < N - w.order
    · exact glSupercuspidalSupportUniqueness.{max uF uV, uF} p F T _ hr D hD _ _
        sdH.support sdS.support
    · have h0 : ∀ s : Multiset (T.CuspidalDatum.{max uF uV, uF}),
          T.IsSupercuspidalSupport D s → s = 0 := fun s hs => by
        by_contra hs0
        exact hr (SegmentHeadSupport.pos_of_isSupercuspidalSupport hs hs0)
      rw [h0 _ sdH.support, h0 _ sdS.support]
  have hcount := congrArg (Multiset.countP P) hsupp
  rw [countP_finset_sum, countP_finset_sum] at hcount
  -- The socle side counts every member with negative exponent.
  have hS : ∑ i, (sdS.factors i).cuspidalSupport.countP P = ∑ i, Lf (dS.segments i) :=
    Finset.sum_congr rfl fun i _ => (sdS.factors i).allowed
  -- The head side misses at least one.
  have hH : ∑ i, ((sdH.factors i).cuspidalSupport.countP P +
      (if 0 < (sdH.factors i).order then 1 else 0)) ≤ ∑ i, Lf (dH.segments i) :=
    Finset.sum_le_sum fun i _ => (sdH.factors i).allowed
  rw [Finset.sum_add_distrib] at hH
  obtain ⟨i0, hi0⟩ : ∃ i, 0 < (sdH.factors i).order := by
    by_contra h
    push Not at h
    have h0 : ∑ i, (sdH.factors i).order = 0 :=
      Finset.sum_eq_zero fun i _ => by have := h i; omega
    have := sdH.order_sum
    have := w.positive
    omega
  have hone : 1 ≤ ∑ i, (if 0 < (sdH.factors i).order then 1 else 0) := by
    have := Finset.single_le_sum (f := fun i => if 0 < (sdH.factors i).order then 1 else 0)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i0)
    simpa [hi0] using this
  have hL : ∑ i, Lf (dH.segments i) = ∑ i, Lf (dS.segments i) := by
    rw [sum_segments_eq dH Lf, sum_segments_eq dS Lf, hdH, hdS]
  omega

end Rectangle

end TadicRectangleHeadSocle

end Langlands.Classification
