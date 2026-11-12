import Langlands.Representation.Aubert.MultisegmentRankOrder
import Langlands.Representation.Classification.TadicMultisegments
import Langlands.Representation.Classification.SegmentReplacementInversions
import Mathlib.Data.Finsupp.Weight

/-!
# Combinatorics of the rectangle `a(n,d)` for Tadić's Proposition 3.8

In positions relative to a cuspidal datum `σ`, `seg σ i l` is the segment
`[ν^i σ, ν^(i+l) σ]` of length `l + 1`, and `rect σ n e` is the multisegment of the `n`
segments `Δ_j = seg σ j e`, `j < n`. Tadić's `a(n,d)^ρ` is `rect σ n (d-1)` for
`σ = ν^(-(n-1)/2-(d-1)/2) ρ`.

For `k + 1 < n`, `adj σ n k e` replaces the linked pair `Δ_k, Δ_(k+1)` by their union and
(nonempty) intersection. We prove, in Zelevinsky's rank order `≼`:

* `adj ≼ rect`, `adj ≠ rect`, and nothing lies strictly between them: the containment
  counts of `adj` are those of `rect` except for the union segment, where they exceed by
  one;
* (Tadić's Lemma 3.4) every `x ≼ rect` contains each `Δ_j` at most once;
* the segment-length weight of a multisegment is the size of its cuspidal content, and
  no submultiset of `adj` avoiding all `Δ_j` has weight `e + 1`.
-/

noncomputable section

open scoped Classical

namespace Langlands.Classification.TadicRectanglePrime

open PadicField.TopologicalData PadicField.TopologicalData.Multisegment

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-! ### Segments in positions -/

/-- The segment `[ν^i σ, ν^(i+l) σ]`, of length `l + 1`. -/
def seg (σ : T.CuspidalDatum.{uV, uF}) (i l : ℕ) : T.Segment.{uV, uF} where
  base := σ.twist (i : ℝ)
  length := l + 1
  length_pos := Nat.succ_pos l

variable (σ : T.CuspidalDatum.{uV, uF})

@[simp]
theorem seg_base (i l : ℕ) : (seg σ i l).base = σ.twist (i : ℝ) := rfl

@[simp]
theorem seg_length (i l : ℕ) : (seg σ i l).length = l + 1 := rfl

theorem seg_member (i l j : ℕ) : (seg σ i l).member j = σ.twist ((i + j : ℕ) : ℝ) :=
  σ.twist_natCast_twist_natCast i j

variable {σ}

/-- Containment of segments in positions: `[i, i+l] ⊆ [i', i'+l']`. -/
theorem seg_subset_iff {i l i' l' : ℕ} :
    (seg σ i l).support ⊆ (seg σ i' l').support ↔ i' ≤ i ∧ i + l ≤ i' + l' := by
  rw [Segment.support_subset_iff]
  constructor
  · rintro ⟨t, hb, hle⟩
    rw [seg_base, seg_member] at hb
    have := σ.twist_natCast_injective hb
    simp only [seg_length] at hle
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨i - i', ?_, ?_⟩
    · rw [seg_base, seg_member, Nat.add_sub_cancel' h1]
    · simp only [seg_length]
      omega

theorem seg_eq_seg_iff {i l i' l' : ℕ} : seg σ i l = seg σ i' l' ↔ i = i' ∧ l = l' := by
  constructor
  · intro h
    have hb := congrArg Segment.base h
    have hl := congrArg Segment.length h
    simp only [seg_base, seg_length] at hb hl
    exact ⟨σ.twist_natCast_injective hb, by omega⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem seg_injective (e : ℕ) : Function.Injective fun j => seg σ j e :=
  fun _ _ h => (seg_eq_seg_iff.mp h).1

/-- A segment contained in a segment in positions is itself in positions. -/
theorem exists_eq_seg_of_subset {I : T.Segment.{uV, uF}} {i l : ℕ}
    (h : I.support ⊆ (seg σ i l).support) : ∃ t l', I = seg σ t l' := by
  obtain ⟨t, hb, -⟩ := Segment.support_subset_iff.mp h
  refine ⟨i + t, I.length - 1, Segment.ext_base_length ?_ ?_⟩
  · rw [hb, seg_member, seg_base]
  · simp only [seg_length]
    have := I.length_pos
    omega

/-- Segments with equal supports are equal. -/
theorem eq_of_support_eq {Δ Δ' : T.Segment.{uV, uF}} (h : Δ.support = Δ'.support) : Δ = Δ' :=
  Segment.eq_of_support_subset_of_length_le h.subset
    (Segment.length_le_of_support_subset h.symm.subset)

/-- The union of two overlapping or juxtaposed segments in positions. -/
theorem seg_support_union (k e : ℕ) :
    (seg σ k (e + 1)).support = (seg σ k e).support ∪ (seg σ (k + 1) e).support := by
  ext τ
  simp only [Segment.support, seg_length, seg_member, Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i, hi, rfl⟩
    by_cases h : i < e + 1
    · exact Or.inl ⟨i, h, rfl⟩
    · refine Or.inr ⟨e, by omega, ?_⟩
      have : k + i = k + 1 + e := by omega
      rw [this]
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · exact ⟨i, by omega, rfl⟩
    · refine ⟨i + 1, by omega, ?_⟩
      have : k + (i + 1) = k + 1 + i := by omega
      rw [this]

/-- `Δ_k` precedes `Δ_(k+1)`. -/
theorem seg_precedes (k e : ℕ) : (seg σ k e).Precedes (seg σ (k + 1) e) := by
  refine ⟨⟨fun h => ?_, fun h => ?_, seg σ k (e + 1), seg_support_union k e⟩, 1, one_pos, ?_⟩
  · rw [seg_subset_iff] at h
    omega
  · rw [seg_subset_iff] at h
    omega
  · rw [seg_base, seg_base]
    exact (σ.twist_natCast_twist_natCast k 1).symm

/-! ### The rectangle and its neighbour -/

/-- The rectangle: the segments `Δ_j = seg σ j e`, `j < n`. -/
def rect (σ : T.CuspidalDatum.{uV, uF}) (n e : ℕ) : T.Multisegment.{uV, uF} :=
  (Multiset.range n).map fun j => seg σ j e

/-- Tadić's `a(n,d)^ρ` in positions. -/
theorem tadicMultisegment_eq_rect (ρ : T.CuspidalDatum.{uV, uF}) (n d : ℕ) (hd : 0 < d) :
    tadicMultisegment ρ n d hd =
      rect (ρ.twist (-(((n : ℝ) - 1) / 2) - ((d : ℝ) - 1) / 2)) n (d - 1) := by
  unfold tadicMultisegment rect
  refine Multiset.map_congr rfl fun j _ => Segment.ext_base_length ?_ ?_
  · simp only [tadicCenteredSegment, seg_base, CuspidalDatum.twist_twist]
    congr 1
    ring
  · simp only [tadicCenteredSegment, seg_length]
    omega

theorem rect_succ (n e : ℕ) : rect σ (n + 1) e = seg σ n e ::ₘ rect σ n e := by
  rw [rect, Multiset.range_succ, Multiset.map_cons]
  rfl

theorem toFinsupp_rect (n e : ℕ) :
    Multiset.toFinsupp (rect σ n e) = ∑ j ∈ Finset.range n, Finsupp.single (seg σ j e) 1 := by
  induction n with
  | zero => simp [rect]
  | succ n ih =>
    rw [rect_succ, ← Multiset.singleton_add, Multiset.toFinsupp_add, Multiset.toFinsupp_singleton,
      ih, Finset.sum_range_succ, add_comm]

/-- The positions of the segments of `rect` other than `Δ_k, Δ_(k+1)`. -/
def restIdx (n k : ℕ) : Multiset ℕ := ((Multiset.range n).erase k).erase (k + 1)

theorem nodup_restIdx (n k : ℕ) : (restIdx n k).Nodup :=
  ((Multiset.nodup_range n).erase k).erase (k + 1)

theorem mem_restIdx {n k j : ℕ} : j ∈ restIdx n k ↔ j ≠ k + 1 ∧ j ≠ k ∧ j < n := by
  rw [restIdx, ((Multiset.nodup_range n).erase k).mem_erase_iff,
    (Multiset.nodup_range n).mem_erase_iff, Multiset.mem_range]

/-- The segments of `rect` other than `Δ_k, Δ_(k+1)`. -/
def rest (σ : T.CuspidalDatum.{uV, uF}) (n k e : ℕ) : T.Multisegment.{uV, uF} :=
  (restIdx n k).map fun j => seg σ j e

theorem rect_eq {n k : ℕ} (e : ℕ) (h : k + 1 < n) :
    rect σ n e = seg σ k e ::ₘ seg σ (k + 1) e ::ₘ rest σ n k e := by
  have h1 : k + 1 ∈ (Multiset.range n).erase k :=
    (Multiset.mem_erase_of_ne (by omega)).mpr (Multiset.mem_range.mpr h)
  have h2 : k ∈ Multiset.range n := Multiset.mem_range.mpr (by omega)
  rw [rect, ← Multiset.cons_erase h2, ← Multiset.cons_erase h1]
  simp only [Multiset.map_cons]
  rfl

theorem rect_eq_pair_add {n k : ℕ} (e : ℕ) (h : k + 1 < n) :
    rect σ n e = ({seg σ (k + 1) e, seg σ k e} : T.Multisegment.{uV, uF}) + rest σ n k e := by
  rw [rect_eq e h, Multiset.insert_eq_cons, Multiset.cons_add, Multiset.singleton_add,
    Multiset.cons_swap]

theorem count_rest (n k e j : ℕ) :
    (rest σ n k e).count (seg σ j e) = if j ∈ restIdx n k then 1 else 0 := by
  rw [rest, Multiset.count_map_eq_count' _ _ (seg_injective e)]
  split_ifs with h
  · exact Multiset.count_eq_one_of_mem (nodup_restIdx n k) h
  · exact Multiset.count_eq_zero_of_notMem h

theorem exists_of_mem_rest {n k e : ℕ} {S : T.Segment.{uV, uF}} (h : S ∈ rest σ n k e) :
    ∃ j < n, S = seg σ j e := by
  obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.mp h
  exact ⟨j, (mem_restIdx.mp hj).2.2, rfl⟩

/-- The intersection `Δ_k ∩ Δ_(k+1)`, omitted when empty (`e = 0`). -/
def capMs (σ : T.CuspidalDatum.{uV, uF}) (k e : ℕ) : T.Multisegment.{uV, uF} :=
  if 1 ≤ e then {seg σ (k + 1) (e - 1)} else 0

/-- Union and intersection of `Δ_k` and `Δ_(k+1)` in place of the pair. -/
def adj (σ : T.CuspidalDatum.{uV, uF}) (n k e : ℕ) : T.Multisegment.{uV, uF} :=
  seg σ k (e + 1) ::ₘ (capMs σ k e + rest σ n k e)

theorem adj_eq_add (n k e : ℕ) :
    adj σ n k e = (seg σ k (e + 1) ::ₘ capMs σ k e) + rest σ n k e := by
  rw [adj, Multiset.cons_add]

/-- The union/intersection replacement of `Δ_(k+1), Δ_k` is `seg σ k (e+1)` together with
`capMs σ k e`. -/
theorem replacement_eq {k e : ℕ} {U : T.Segment.{uV, uF}} {I : Option T.Segment.{uV, uF}}
    (h : (seg σ (k + 1) e).IsUnionIntersectionReplacement (seg σ k e) U I) :
    ((U :: I.toList : List _) : T.Multisegment.{uV, uF}) = seg σ k (e + 1) ::ₘ capMs σ k e := by
  obtain ⟨hU, hI⟩ := h
  have hU' : U = seg σ k (e + 1) := by
    rw [Set.union_comm, ← seg_support_union] at hU
    exact eq_of_support_eq hU
  subst hU'
  cases I with
  | none =>
    have he : e = 0 := by
      by_contra he
      have h1 : (seg σ (k + 1) 0).support ⊆ (seg σ (k + 1) e).support :=
        seg_subset_iff.mpr ⟨le_rfl, by omega⟩
      have h2 : (seg σ (k + 1) 0).support ⊆ (seg σ k e).support :=
        seg_subset_iff.mpr ⟨by omega, by omega⟩
      have hm := (Set.subset_inter h1 h2) (seg σ (k + 1) 0).base_mem_support
      rw [hI] at hm
      exact hm
    subst he
    simp [capMs]
  | some J =>
    change J.support = _ at hI
    have hJ1 : J.support ⊆ (seg σ (k + 1) e).support := hI ▸ Set.inter_subset_left
    have hJ2 : J.support ⊆ (seg σ k e).support := hI ▸ Set.inter_subset_right
    obtain ⟨t, l, rfl⟩ := exists_eq_seg_of_subset hJ2
    rw [seg_subset_iff] at hJ1 hJ2
    have he : 1 ≤ e := by omega
    have hc1 : (seg σ (k + 1) (e - 1)).support ⊆ (seg σ (k + 1) e).support :=
      seg_subset_iff.mpr ⟨le_rfl, by omega⟩
    have hc2 : (seg σ (k + 1) (e - 1)).support ⊆ (seg σ k e).support :=
      seg_subset_iff.mpr ⟨by omega, by omega⟩
    have hc := Set.subset_inter hc1 hc2
    rw [← hI, seg_subset_iff] at hc
    have ht : t = k + 1 := by omega
    have hl : l = e - 1 := by omega
    subst ht hl
    simp only [capMs, ite_eq_left he]
    rfl

/-! ### Containment counts -/

theorem containmentCount_capMs (I : T.Segment.{uV, uF}) (k e : ℕ) :
    containmentCount I (capMs σ k e) =
      if 1 ≤ e ∧ I.support ⊆ (seg σ (k + 1) (e - 1)).support then 1 else 0 := by
  unfold capMs
  by_cases he : 1 ≤ e
  · simp only [he, ite_true, true_and]
    rw [← Multiset.cons_zero, containmentCount_cons, containmentCount_zero, zero_add]
  · simp [he]

/-- The containment counts of `adj` exceed those of `rect` exactly at the union. -/
theorem containmentCount_adj (I : T.Segment.{uV, uF}) {n k : ℕ} (e : ℕ) (h : k + 1 < n) :
    containmentCount I (adj σ n k e) =
      containmentCount I (rect σ n e) + if I = seg σ k (e + 1) then 1 else 0 := by
  rw [rect_eq e h, adj, containmentCount_cons, containmentCount_add, containmentCount_capMs,
    containmentCount_cons, containmentCount_cons]
  by_cases hU : I.support ⊆ (seg σ k (e + 1)).support
  · obtain ⟨t, l, rfl⟩ := exists_eq_seg_of_subset hU
    rw [seg_subset_iff] at hU
    simp only [seg_subset_iff, seg_eq_seg_iff]
    split_ifs <;> omega
  · have h1 : ¬ I.support ⊆ (seg σ k e).support := fun h' =>
      hU (h'.trans (seg_subset_iff.mpr ⟨le_rfl, by omega⟩))
    have h2 : ¬ I.support ⊆ (seg σ (k + 1) e).support := fun h' =>
      hU (h'.trans (seg_subset_iff.mpr ⟨by omega, by omega⟩))
    have h3 : ¬ (1 ≤ e ∧ I.support ⊆ (seg σ (k + 1) (e - 1)).support) := fun h' =>
      hU (h'.2.trans (seg_subset_iff.mpr ⟨by omega, by omega⟩))
    have h4 : I ≠ seg σ k (e + 1) := fun h' => hU (h' ▸ subset_rfl)
    simp only [hU, h1, h2, h3, h4, ite_false]
    omega

/-- Equal counts on one-element segments give equal cuspidal content. -/
theorem cuspidalContent_eq_of_containmentCount {a b : T.Multisegment.{uV, uF}}
    (h : ∀ I : T.Segment.{uV, uF}, I.length = 1 → containmentCount I a = containmentCount I b) :
    a.cuspidalContent = b.cuspidalContent := by
  ext ρ
  rw [← containmentCount_singletonSegment, ← containmentCount_singletonSegment]
  exact h _ rfl

theorem containmentCount_eq_of_cuspidalContent_eq {a b : T.Multisegment.{uV, uF}}
    (h : a.cuspidalContent = b.cuspidalContent) {I : T.Segment.{uV, uF}} (hI : I.length = 1) :
    containmentCount I a = containmentCount I b := by
  rw [Segment.eq_singletonSegment_of_length_eq_one hI, containmentCount_singletonSegment,
    containmentCount_singletonSegment, h]

theorem rankLE_adj {n k : ℕ} (e : ℕ) (h : k + 1 < n) : RankLE (adj σ n k e) (rect σ n e) := by
  refine ⟨cuspidalContent_eq_of_containmentCount fun I hI => ?_, fun I => ?_⟩
  · have : I ≠ seg σ k (e + 1) := fun h' => by
      rw [h', seg_length] at hI
      omega
    rw [containmentCount_adj I e h, ite_eq_right this, add_zero]
  · rw [containmentCount_adj I e h]
    omega

theorem adj_ne_rect {n k : ℕ} (e : ℕ) (h : k + 1 < n) : adj σ n k e ≠ rect σ n e := by
  intro h'
  have := containmentCount_adj (σ := σ) (seg σ k (e + 1)) e h
  rw [h', ite_eq_left rfl] at this
  omega

/-- Nothing lies strictly between `adj` and `rect` in the rank order. -/
theorem eq_adj_of_rankLE {n k : ℕ} (e : ℕ) (h : k + 1 < n) {b : T.Multisegment.{uV, uF}}
    (h1 : RankLE (adj σ n k e) b) (h2 : RankLE b (rect σ n e)) (hne : b ≠ rect σ n e) :
    b = adj σ n k e := by
  have hI : ∀ I, I ≠ seg σ k (e + 1) →
      containmentCount I b = containmentCount I (rect σ n e) := fun I hI => by
    have h1' := h1.2 I
    have h2' := h2.2 I
    rw [containmentCount_adj I e h, ite_eq_right hI] at h1'
    omega
  have hU1 := h1.2 (seg σ k (e + 1))
  have hU2 := h2.2 (seg σ k (e + 1))
  rw [containmentCount_adj _ e h, ite_eq_left rfl] at hU1
  by_cases hU : containmentCount (seg σ k (e + 1)) b = containmentCount (seg σ k (e + 1)) (rect σ n e)
  · exact absurd (eq_of_containmentCount_eq fun I => by
      by_cases hI' : I = seg σ k (e + 1)
      · rw [hI']
        exact hU
      · exact hI I hI') hne
  · refine eq_of_containmentCount_eq fun I => ?_
    rw [containmentCount_adj I e h]
    by_cases hI' : I = seg σ k (e + 1)
    · rw [ite_eq_left hI', hI']
      omega
    · rw [ite_eq_right hI', add_zero]
      exact hI I hI'

/-! ### Tadić's Lemma 3.4 -/

/-- Each copy of `Δ_j` contains the end `ν^(j+e) σ` but not `[ν^(j+e) σ, ν^(j+e+1) σ]`. -/
theorem count_add_containmentCount_le (x : T.Multisegment.{uV, uF}) (j e : ℕ) :
    x.count (seg σ j e) + containmentCount (seg σ (j + e) 1) x ≤
      containmentCount (seg σ (j + e) 0) x := by
  induction x using Multiset.induction_on with
  | empty => simp
  | cons S x ih =>
    rw [Multiset.count_cons, containmentCount_cons, containmentCount_cons]
    by_cases hS : seg σ j e = S
    · subst hS
      have h1 : ¬ (seg σ (j + e) 1).support ⊆ (seg σ j e).support := by
        rw [seg_subset_iff]
        omega
      have h2 : (seg σ (j + e) 0).support ⊆ (seg σ j e).support := by
        rw [seg_subset_iff]
        omega
      simp only [h1, h2, ite_true, ite_false]
      omega
    · have h3 : (seg σ (j + e) 0).support ⊆ (seg σ (j + e) 1).support := by
        rw [seg_subset_iff]
        omega
      simp only [hS, ite_false]
      split_ifs with h4 h5
      · omega
      · exact absurd (h3.trans h4) h5
      · omega
      · omega

theorem containmentCount_rect_le (n j e : ℕ) :
    containmentCount (seg σ (j + e) 0) (rect σ n e) ≤
      containmentCount (seg σ (j + e) 1) (rect σ n e) + if j < n then 1 else 0 := by
  induction n with
  | zero => simp [rect]
  | succ n ih =>
    rw [rect_succ, containmentCount_cons, containmentCount_cons]
    simp only [seg_subset_iff]
    split_ifs at ih ⊢ <;> omega

/-- **Tadić 1986, Lemma 3.4.** A multisegment below `rect σ n e` in the rank order contains
each `Δ_j` at most once. -/
theorem count_le_one_of_rankLE {x : T.Multisegment.{uV, uF}} {n e : ℕ}
    (hx : RankLE x (rect σ n e)) (j : ℕ) : x.count (seg σ j e) ≤ 1 := by
  have h1 := count_add_containmentCount_le (σ := σ) x j e
  have h2 := containmentCount_rect_le (σ := σ) n j e
  have h3 := hx.2 (seg σ (j + e) 1)
  have h4 := containmentCount_eq_of_cuspidalContent_eq hx.1 (I := seg σ (j + e) 0) rfl
  split_ifs at h2 <;> omega

/-! ### Weights -/

/-- The segment-length weight of a multisegment is the size of its cuspidal content. -/
theorem weight_toFinsupp (x : T.Multisegment.{uV, uF}) :
    Finsupp.weight (fun S : T.Segment.{uV, uF} => S.length) (Multiset.toFinsupp x) =
      Multiset.card x.cuspidalContent := by
  induction x using Multiset.induction_on with
  | empty => simp
  | cons S x ih =>
    rw [← Multiset.singleton_add, Multiset.toFinsupp_add, map_add, Multiset.toFinsupp_singleton,
      Finsupp.weight_single, ih, cuspidalContent_add, Multiset.card_add, cuspidalContent_singleton,
      Segment.card_cuspidalContent, one_smul]

theorem count_adj_left {n k : ℕ} (e : ℕ) : (adj σ n k e).count (seg σ k e) = 0 := by
  rw [adj, Multiset.count_cons, Multiset.count_add, count_rest, capMs]
  have h1 : seg σ k e ≠ seg σ k (e + 1) := fun h => by
    rw [seg_eq_seg_iff] at h
    omega
  have h2 : k ∉ restIdx n k := fun h => (mem_restIdx.mp h).2.1 rfl
  split_ifs with he
  · rw [Multiset.count_singleton, ite_eq_right (fun h => by rw [seg_eq_seg_iff] at h; omega)]
  · simp

theorem count_adj_right {n k : ℕ} (e : ℕ) : (adj σ n k e).count (seg σ (k + 1) e) = 0 := by
  rw [adj, Multiset.count_cons, Multiset.count_add, count_rest, capMs]
  have h1 : seg σ (k + 1) e ≠ seg σ k (e + 1) := fun h => by
    rw [seg_eq_seg_iff] at h
    omega
  have h2 : k + 1 ∉ restIdx n k := fun h => (mem_restIdx.mp h).1 rfl
  split_ifs with he
  · rw [Multiset.count_singleton, ite_eq_right (fun h => by rw [seg_eq_seg_iff] at h; omega)]
  · simp

theorem count_adj_of_ne {n k j : ℕ} (e : ℕ) (hj : j < n) (hk : j ≠ k) (hk1 : j ≠ k + 1) :
    (adj σ n k e).count (seg σ j e) = 1 := by
  rw [adj, Multiset.count_cons, Multiset.count_add, count_rest, capMs,
    ite_eq_left (mem_restIdx.mpr ⟨hk1, hk, hj⟩)]
  have h1 : seg σ j e ≠ seg σ k (e + 1) := fun h => by
    rw [seg_eq_seg_iff] at h
    omega
  split_ifs with he
  · rw [Multiset.count_singleton, ite_eq_right (fun h => by rw [seg_eq_seg_iff] at h; omega)]
  · simp

/-- The submultisets of `seg σ k (e+1) ::ₘ capMs σ k e` have content size `0`, `e`, `e + 2`
or `2e + 2`, never `e + 1`. -/
theorem card_cuspidalContent_ne_of_le {k e : ℕ} {x : T.Multisegment.{uV, uF}}
    (hle : x ≤ seg σ k (e + 1) ::ₘ capMs σ k e) :
    Multiset.card x.cuspidalContent ≠ e + 1 := by
  by_cases hU : seg σ k (e + 1) ∈ x
  · obtain ⟨x', rfl⟩ := Multiset.exists_cons_of_mem hU
    rw [cuspidalContent_cons, Multiset.card_add, Segment.card_cuspidalContent, seg_length]
    omega
  · rw [Multiset.le_cons_of_notMem hU, capMs] at hle
    split_ifs at hle with he
    · rcases Multiset.le_singleton.mp hle with rfl | rfl
      · simp
      · rw [cuspidalContent_singleton, Segment.card_cuspidalContent, seg_length]
        omega
    · rw [Multiset.le_zero.mp hle]
      simp

/-- No submultiset of `adj` avoiding every `Δ_j` has weight `e + 1`. -/
theorem weight_ne_of_le_adj {n k : ℕ} (e : ℕ) {ν : T.Segment.{uV, uF} →₀ ℕ}
    (hν : ν ≤ Multiset.toFinsupp (adj σ n k e)) (h0 : ∀ j < n, ν (seg σ j e) = 0) :
    Finsupp.weight (fun S : T.Segment.{uV, uF} => S.length) ν ≠ e + 1 := by
  have hνx : ν = Multiset.toFinsupp (Finsupp.toMultiset ν) := by
    rw [Finsupp.toMultiset_toFinsupp]
  rw [hνx, weight_toFinsupp]
  refine card_cuspidalContent_ne_of_le (σ := σ) (k := k) (Multiset.le_iff_count.mpr fun S => ?_)
  have hS := hν S
  rw [Multiset.toFinsupp_apply, adj_eq_add, Multiset.count_add] at hS
  rw [Finsupp.count_toMultiset]
  by_cases hm : S ∈ rest σ n k e
  · obtain ⟨j, hj, rfl⟩ := exists_of_mem_rest hm
    rw [h0 j hj]
    exact Nat.zero_le _
  · rw [Multiset.count_eq_zero_of_notMem hm, add_zero] at hS
    exact hS

end Langlands.Classification.TadicRectanglePrime
