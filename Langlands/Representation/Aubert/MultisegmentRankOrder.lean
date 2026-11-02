import Langlands.Representation.Classification.SegmentInitialTruncation
import Langlands.Representation.Classification.SegmentCuspidalContent
import Langlands.Representation.Classification.SegmentSupportContainment
import Langlands.Representation.Classification.CuspidalIntegralTwistFreenessProof
import Langlands.Representation.Classification.SingletonSegmentSocle

/-!
# Containment counts and the rank order on multisegments

For a segment `I` and a multisegment `a`, `containmentCount I a` is the number of
segment occurrences of `a` whose support contains the support of `I`. The rank
order `b ≼ a` asks that `a` and `b` have the same cuspidal content and that every
containment count of `b` is at least that of `a`. It is a well-founded partial
order once strictness is required, and it satisfies the combinatorial step `(*)`
of Zelevinsky's proof of Theorem 7.1: if `b⁻ ≼ c + S⁻` and `a = c + S` have the
cuspidal content of `b`, then `b ≼ a`.
-/

noncomputable section

namespace Langlands.PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

open scoped Classical

namespace CuspidalDatum

/-- `ν^j (ν^i ρ) = ν^(i+j) ρ` for natural exponents. -/
theorem twist_natCast_twist_natCast (ρ : CuspidalDatum.{uV, uF} T) (i j : ℕ) :
    (ρ.twist ((i : ℕ) : ℝ)).twist ((j : ℕ) : ℝ) = ρ.twist ((i + j : ℕ) : ℝ) := by
  rw [twist_twist]
  congr 1
  push_cast
  ring

/-- Integral twist-freeness in natural form: `ν^i ρ = ν^j ρ` forces `i = j`. -/
theorem twist_natCast_injective (ρ : CuspidalDatum.{uV, uF} T) {i j : ℕ}
    (h : ρ.twist ((i : ℕ) : ℝ) = ρ.twist ((j : ℕ) : ℝ)) : i = j := by
  have hz : ρ.twist (((i : ℤ) - (j : ℤ) : ℤ) : ℝ) = ρ := by
    calc
      _ = (ρ.twist ((i : ℕ) : ℝ)).twist (-((j : ℕ) : ℝ)) := by
        rw [twist_twist]
        congr 1
        push_cast
        ring
      _ = (ρ.twist ((j : ℕ) : ℝ)).twist (-((j : ℕ) : ℝ)) :=
        congrArg (fun x => x.twist (-((j : ℕ) : ℝ))) h
      _ = ρ := by rw [twist_twist, neg_add_cancel, twist_zero]
  have := (Classification.cuspidalIntegralTwistFreeness F T ρ ((i : ℤ) - (j : ℤ))).mp hz
  omega

end CuspidalDatum

namespace Segment

/-- The members of a segment are pairwise distinct. -/
theorem member_injective (Δ : Segment.{uV, uF} T) {i j : ℕ}
    (h : Δ.member i = Δ.member j) : i = j :=
  Δ.base.twist_natCast_injective h

theorem member_twist_natCast (Δ : Segment.{uV, uF} T) (i j : ℕ) :
    (Δ.member i).twist ((j : ℕ) : ℝ) = Δ.member (i + j) :=
  Δ.base.twist_natCast_twist_natCast i j

/-- A segment is determined by its beginning and its length. -/
theorem ext_base_length {Δ Δ' : Segment.{uV, uF} T} (hb : Δ.base = Δ'.base)
    (hl : Δ.length = Δ'.length) : Δ = Δ' := by
  cases Δ
  cases Δ'
  cases hb
  cases hl
  rfl

/-- Containment of supports in positional form: `I ⊆ Δ` exactly when `I` begins at
some position `i` of `Δ` and ends inside `Δ`. -/
theorem support_subset_iff {I Δ : Segment.{uV, uF} T} :
    I.support ⊆ Δ.support ↔ ∃ i, I.base = Δ.member i ∧ i + I.length ≤ Δ.length := by
  constructor
  · intro h
    obtain ⟨i, hi, hbi⟩ := h I.base_mem_support
    obtain ⟨j, hj, hlj⟩ := h I.last_mem_support
    refine ⟨i, hbi.symm, ?_⟩
    have hlast : I.last = Δ.member (i + (I.length - 1)) := by
      rw [← Δ.member_twist_natCast, hbi]
      rfl
    have := Δ.member_injective (hlj.trans hlast)
    have := I.length_pos
    omega
  · rintro ⟨i, hb, hle⟩
    exact support_subset_of_base_shift hb hle

theorem length_le_of_support_subset {I Δ : Segment.{uV, uF} T}
    (h : I.support ⊆ Δ.support) : I.length ≤ Δ.length := by
  obtain ⟨i, -, hle⟩ := support_subset_iff.mp h
  omega

/-- A segment contained in a segment of at most its length is that segment. -/
theorem eq_of_support_subset_of_length_le {I Δ : Segment.{uV, uF} T}
    (h : I.support ⊆ Δ.support) (hl : Δ.length ≤ I.length) : I = Δ := by
  obtain ⟨i, hb, hle⟩ := support_subset_iff.mp h
  have hi : i = 0 := by omega
  subst hi
  exact ext_base_length (by simpa using hb) (by omega)

/-- Deleting the end shrinks the support. -/
theorem dropLastNonempty_support_subset (I : Segment.{uV, uF} T) (h : 1 < I.length) :
    (I.dropLastNonempty h).support ⊆ I.support :=
  support_subset_iff.mpr ⟨0, by simp, by simp⟩

/-- For segments of length at least two, containment is unchanged by deleting both
ends. -/
theorem dropLastNonempty_support_subset_iff {I Δ : Segment.{uV, uF} T}
    (hI : 1 < I.length) (hΔ : 1 < Δ.length) :
    (I.dropLastNonempty hI).support ⊆ (Δ.dropLastNonempty hΔ).support ↔
      I.support ⊆ Δ.support := by
  rw [support_subset_iff, support_subset_iff]
  simp only [dropLastNonempty_base, dropLastNonempty_length, dropLastNonempty_member]
  constructor
  · rintro ⟨i, hb, hle⟩
    exact ⟨i, hb, by omega⟩
  · rintro ⟨i, hb, hle⟩
    exact ⟨i, hb, by omega⟩

/-- The members of a segment, listed once each, have no repetition. -/
theorem cuspidalContent_nodup (Δ : Segment.{uV, uF} T) : Δ.cuspidalContent.Nodup := by
  rw [cuspidalContent, Multiset.coe_nodup, List.nodup_ofFn]
  intro i j h
  exact Fin.ext (Δ.member_injective h)

/-- The published one-member segment `[ρ]` is contained in `Δ` exactly when `ρ` is a
member of `Δ`. -/
theorem singletonSegment_support_subset_iff (ρ : CuspidalDatum.{uV, uF} T)
    (Δ : Segment.{uV, uF} T) : (T.singletonSegment ρ).support ⊆ Δ.support ↔ ρ ∈ Δ.support := by
  rw [support_subset_iff]
  constructor
  · rintro ⟨i, hb, hle⟩
    exact ⟨i, by simp [singletonSegment] at hle; omega, hb.symm⟩
  · rintro ⟨i, hi, hb⟩
    exact ⟨i, hb.symm, by simp [singletonSegment]; omega⟩

theorem eq_singletonSegment_of_length_eq_one {I : Segment.{uV, uF} T} (h : I.length = 1) :
    I = T.singletonSegment I.base :=
  ext_base_length rfl h

end Segment

namespace Multisegment

open Segment

/-- Zelevinsky's `a⁻`: replace every segment `Δ` by `Δ⁻`, omitting the empty
outcomes of one-element segments. -/
def dropLast (a : Multisegment.{uV, uF} T) : Multisegment.{uV, uF} T :=
  a.filterMap Segment.dropLast

@[simp]
theorem dropLast_zero : dropLast (0 : Multisegment.{uV, uF} T) = 0 := rfl

/-- On a list of segments, `a⁻` is the published list truncation `dropLastList`. -/
theorem dropLast_coe (l : List (Segment.{uV, uF} T)) :
    dropLast (l : Multisegment.{uV, uF} T) = (Segment.dropLastList l : Multisegment.{uV, uF} T) :=
  Multiset.filterMap_coe _ _

theorem dropLast_add (a b : Multisegment.{uV, uF} T) :
    dropLast (a + b) = dropLast a + dropLast b :=
  Multiset.filterMap_add _ _ _

theorem dropLast_cons_of_one_lt (Δ : Segment.{uV, uF} T) (h : 1 < Δ.length)
    (a : Multisegment.{uV, uF} T) :
    dropLast (Δ ::ₘ a) = Δ.dropLastNonempty h ::ₘ dropLast a :=
  Multiset.filterMap_cons_some _ _ _ (Δ.dropLast_of_one_lt h)

theorem dropLast_cons_of_length_eq_one (Δ : Segment.{uV, uF} T) (h : Δ.length = 1)
    (a : Multisegment.{uV, uF} T) : dropLast (Δ ::ₘ a) = dropLast a :=
  Multiset.filterMap_cons_none _ _ (Δ.dropLast_of_length_eq_one h)

open scoped Classical in
/-- The number of segment occurrences of `a` containing the segment `I`. -/
def containmentCount (I : Segment.{uV, uF} T) (a : Multisegment.{uV, uF} T) : ℕ :=
  a.countP fun Δ => I.support ⊆ Δ.support

@[simp]
theorem containmentCount_zero (I : Segment.{uV, uF} T) :
    containmentCount I (0 : Multisegment.{uV, uF} T) = 0 := by
  classical
  simp [containmentCount]

theorem containmentCount_add (I : Segment.{uV, uF} T) (a b : Multisegment.{uV, uF} T) :
    containmentCount I (a + b) = containmentCount I a + containmentCount I b := by
  classical
  simp [containmentCount, Multiset.countP_add]

theorem containmentCount_cons (I Δ : Segment.{uV, uF} T) (a : Multisegment.{uV, uF} T) :
    containmentCount I (Δ ::ₘ a) =
      containmentCount I a + if I.support ⊆ Δ.support then 1 else 0 := by
  classical
  simp only [containmentCount, Multiset.countP_cons]

/-- Containment counts decrease when the contained segment grows. -/
theorem containmentCount_mono {I J : Segment.{uV, uF} T} (h : I.support ⊆ J.support)
    (a : Multisegment.{uV, uF} T) : containmentCount J a ≤ containmentCount I a := by
  classical
  induction a using Multiset.induction_on with
  | empty => simp
  | cons Δ a ih =>
    rw [containmentCount_cons, containmentCount_cons]
    by_cases hJ : J.support ⊆ Δ.support
    · simp only [hJ, h.trans hJ, ↓reduceIte]
      omega
    · simp only [hJ, ↓reduceIte]
      split_ifs <;> omega

theorem containmentCount_pos_iff (I : Segment.{uV, uF} T) (a : Multisegment.{uV, uF} T) :
    0 < containmentCount I a ↔ ∃ Δ ∈ a, I.support ⊆ Δ.support := by
  classical
  simp [containmentCount, Multiset.countP_pos]

theorem containmentCount_le_card (I : Segment.{uV, uF} T) (a : Multisegment.{uV, uF} T) :
    containmentCount I a ≤ Multiset.card a := by
  classical
  exact Multiset.countP_le_card _ _

/-- A one-element segment `[ρ]` is contained in exactly as many segment occurrences
as `ρ` has occurrences in the cuspidal content. -/
theorem containmentCount_singletonSegment (ρ : CuspidalDatum.{uV, uF} T)
    (a : Multisegment.{uV, uF} T) :
    containmentCount (T.singletonSegment ρ) a = a.cuspidalContent.count ρ := by
  classical
  induction a using Multiset.induction_on with
  | empty => simp
  | cons Δ a ih =>
    rw [containmentCount_cons, cuspidalContent_cons, Multiset.count_add, ih,
      singletonSegment_support_subset_iff]
    by_cases hρ : ρ ∈ Δ.support
    · simp only [hρ, ↓reduceIte]
      rw [Multiset.count_eq_one_of_mem Δ.cuspidalContent_nodup
        ((Δ.mem_cuspidalContent ρ).mpr hρ), add_comm]
    · simp only [hρ, ↓reduceIte]
      rw [Multiset.count_eq_zero_of_notMem
        (fun h => hρ ((Δ.mem_cuspidalContent ρ).mp h))]
      simp

/-- Deleting all ends: `I⁻ ⊆ Δ⁻` in `a⁻` exactly when `I ⊆ Δ` in `a`, for `I` of
length at least two. -/
theorem containmentCount_dropLast (I : Segment.{uV, uF} T) (hI : 1 < I.length)
    (a : Multisegment.{uV, uF} T) :
    containmentCount (I.dropLastNonempty hI) a.dropLast = containmentCount I a := by
  classical
  induction a using Multiset.induction_on with
  | empty => simp
  | cons Δ a ih =>
    by_cases hΔ : 1 < Δ.length
    · rw [dropLast_cons_of_one_lt Δ hΔ, containmentCount_cons, containmentCount_cons, ih,
        dropLastNonempty_support_subset_iff hI hΔ]
    · have hΔ1 : Δ.length = 1 := by have := Δ.length_pos; omega
      rw [dropLast_cons_of_length_eq_one Δ hΔ1, containmentCount_cons, ih]
      have : ¬ I.support ⊆ Δ.support := fun h => by
        have := length_le_of_support_subset h
        omega
      simp only [this, ↓reduceIte, add_zero]

/-- Zelevinsky's subordination step: shortening some segments of `a = c + S` to
`c + S⁻` does not decrease the count of `I⁻`, for `I` of length at least two. -/
theorem containmentCount_le_subordinate (I : Segment.{uV, uF} T) (hI : 1 < I.length)
    (c S : Multisegment.{uV, uF} T) :
    containmentCount I (c + S) ≤ containmentCount (I.dropLastNonempty hI) (c + S.dropLast) := by
  rw [containmentCount_add, containmentCount_add, containmentCount_dropLast I hI]
  exact Nat.add_le_add_right
    (containmentCount_mono (I.dropLastNonempty_support_subset hI) c) _

/-- A segment of maximal length in `a` is counted only by its own occurrences. -/
theorem containmentCount_eq_count_of_maximal (Δ : Segment.{uV, uF} T)
    (a : Multisegment.{uV, uF} T) (hmax : ∀ Δ' ∈ a, Δ'.length ≤ Δ.length) :
    containmentCount Δ a = a.count Δ := by
  classical
  unfold containmentCount
  change _ = Multiset.countP (Δ = ·) a
  apply Multiset.countP_congr rfl
  intro Δ' hΔ'
  apply propext
  constructor
  · intro h
    exact eq_of_support_subset_of_length_le h (hmax Δ' hΔ')
  · rintro rfl
    exact subset_rfl

/-- Containment counts determine a multisegment. -/
theorem eq_of_containmentCount_eq {a b : Multisegment.{uV, uF} T}
    (h : ∀ I, containmentCount I a = containmentCount I b) : a = b := by
  classical
  suffices H : ∀ n (a b : Multisegment.{uV, uF} T),
      Multiset.card a + Multiset.card b ≤ n →
        (∀ I, containmentCount I a = containmentCount I b) → a = b from
    H _ a b le_rfl h
  intro n
  induction n with
  | zero =>
    intro a b hn _
    have ha : Multiset.card a = 0 := by omega
    have hb : Multiset.card b = 0 := by omega
    rw [Multiset.card_eq_zero.mp ha, Multiset.card_eq_zero.mp hb]
  | succ n ih =>
    intro a b hn hab
    by_cases h0 : a + b = 0
    · obtain ⟨ha0, hb0⟩ := add_eq_zero.mp h0
      rw [ha0, hb0]
    obtain ⟨Δ, hΔ, hmax⟩ := Multiset.exists_max_image Segment.length h0
    have hca := containmentCount_eq_count_of_maximal Δ a
      (fun Δ' h' => hmax Δ' (Multiset.mem_add.mpr (Or.inl h')))
    have hcb := containmentCount_eq_count_of_maximal Δ b
      (fun Δ' h' => hmax Δ' (Multiset.mem_add.mpr (Or.inr h')))
    have hcount : a.count Δ = b.count Δ := by rw [← hca, ← hcb, hab]
    have hpos : 0 < a.count Δ + b.count Δ := by
      rw [← Multiset.count_add]
      exact Multiset.count_pos.mpr hΔ
    have ha : Δ ∈ a := Multiset.count_pos.mp (by omega)
    have hb : Δ ∈ b := Multiset.count_pos.mp (by omega)
    rw [← Multiset.cons_erase ha, ← Multiset.cons_erase hb]
    congr 1
    apply ih
    · have h1 := Multiset.card_erase_add_one ha
      have h2 := Multiset.card_erase_add_one hb
      omega
    · intro I
      have := hab I
      rw [← Multiset.cons_erase ha, ← Multiset.cons_erase hb, containmentCount_cons,
        containmentCount_cons] at this
      omega

/-- The rank order `b ≼ a`: equal cuspidal content and every containment count of
`b` at least that of `a`. It replaces Zelevinsky's order of Ze80 §7.1 in the proof of
Ze80 Theorem 7.1. -/
def RankLE (b a : Multisegment.{uV, uF} T) : Prop :=
  b.cuspidalContent = a.cuspidalContent ∧ ∀ I, containmentCount I a ≤ containmentCount I b

theorem RankLE.refl (a : Multisegment.{uV, uF} T) : RankLE a a :=
  ⟨rfl, fun _ => le_rfl⟩

theorem RankLE.trans {a b c : Multisegment.{uV, uF} T} (hab : RankLE a b)
    (hbc : RankLE b c) : RankLE a c :=
  ⟨hab.1.trans hbc.1, fun I => (hbc.2 I).trans (hab.2 I)⟩

theorem RankLE.antisymm {a b : Multisegment.{uV, uF} T} (hab : RankLE a b)
    (hba : RankLE b a) : a = b :=
  eq_of_containmentCount_eq fun I => le_antisymm (hba.2 I) (hab.2 I)

/-- Zelevinsky's step `(*)` of §7.4 for the rank order: if `b` and `a = c + S` have
the same cuspidal content and `b⁻ ≼ c + S⁻`, then `b ≼ a`. -/
theorem RankLE.of_dropLast {a b c S : Multisegment.{uV, uF} T} (ha : a = c + S)
    (hcont : b.cuspidalContent = a.cuspidalContent)
    (h : RankLE b.dropLast (c + S.dropLast)) : RankLE b a := by
  refine ⟨hcont, fun I => ?_⟩
  by_cases hI : 1 < I.length
  · calc
      containmentCount I a ≤ containmentCount (I.dropLastNonempty hI) (c + S.dropLast) := by
        rw [ha]
        exact containmentCount_le_subordinate I hI c S
      _ ≤ containmentCount (I.dropLastNonempty hI) b.dropLast := h.2 _
      _ = containmentCount I b := containmentCount_dropLast I hI b
  · have hI1 : I.length = 1 := by have := I.length_pos; omega
    rw [eq_singletonSegment_of_length_eq_one hI1, containmentCount_singletonSegment,
      containmentCount_singletonSegment, hcont]

/-- The candidate segments for a cuspidal content `φ`: those beginning at a member
of `φ` with length at most the cardinality of `φ`. -/
def candidateSegments (φ : Multiset (CuspidalDatum.{uV, uF} T)) :
    Finset (Segment.{uV, uF} T) := by
  classical
  exact (φ.toFinset ×ˢ Finset.range (Multiset.card φ)).image
    fun x => (⟨x.1, x.2 + 1, Nat.succ_pos _⟩ : Segment.{uV, uF} T)

theorem cuspidalContent_le_of_mem {Δ : Segment.{uV, uF} T} {a : Multisegment.{uV, uF} T}
    (h : Δ ∈ a) : Δ.cuspidalContent ≤ a.cuspidalContent := by
  rw [← Multiset.cons_erase h, cuspidalContent_cons]
  exact Multiset.le_add_right _ _

theorem mem_candidateSegments {I Δ : Segment.{uV, uF} T} {a : Multisegment.{uV, uF} T}
    (hΔ : Δ ∈ a) (hI : I.support ⊆ Δ.support) : I ∈ candidateSegments a.cuspidalContent := by
  classical
  have hle := cuspidalContent_le_of_mem hΔ
  have hbase : I.base ∈ a.cuspidalContent :=
    Multiset.mem_of_le hle ((Δ.mem_cuspidalContent _).mpr (hI I.base_mem_support))
  have hlen : I.length ≤ Multiset.card a.cuspidalContent := by
    have h1 := length_le_of_support_subset hI
    have h2 := Multiset.card_le_card hle
    rw [card_cuspidalContent] at h2
    omega
  unfold candidateSegments
  rw [Finset.mem_image]
  refine ⟨(I.base, I.length - 1), ?_, ?_⟩
  · rw [Finset.mem_product, Multiset.mem_toFinset, Finset.mem_range]
    have := I.length_pos
    exact ⟨hbase, by omega⟩
  · exact ext_base_length rfl (by have := I.length_pos; simp; omega)

/-- The rank measure: the sum of the containment counts over candidate segments of a
fixed cuspidal content. -/
def rankMeasure (φ : Multiset (CuspidalDatum.{uV, uF} T)) (a : Multisegment.{uV, uF} T) : ℕ :=
  ∑ I ∈ candidateSegments φ, containmentCount I a

theorem card_le_card_cuspidalContent (a : Multisegment.{uV, uF} T) :
    Multiset.card a ≤ Multiset.card a.cuspidalContent := by
  induction a using Multiset.induction_on with
  | empty => simp
  | cons Δ a ih =>
    rw [cuspidalContent_cons, Multiset.card_add, Multiset.card_cons, card_cuspidalContent]
    have := Δ.length_pos
    omega

theorem rankMeasure_le (a : Multisegment.{uV, uF} T) :
    rankMeasure a.cuspidalContent a ≤
      (candidateSegments a.cuspidalContent).card * Multiset.card a.cuspidalContent := by
  unfold rankMeasure
  calc
    ∑ I ∈ candidateSegments a.cuspidalContent, containmentCount I a ≤
        ∑ _I ∈ candidateSegments a.cuspidalContent, Multiset.card a.cuspidalContent :=
      Finset.sum_le_sum fun I _ =>
        (containmentCount_le_card I a).trans (card_le_card_cuspidalContent a)
    _ = _ := by rw [Finset.sum_const, smul_eq_mul]

/-- A strict rank inequality strictly increases the rank measure. -/
theorem rankMeasure_lt {a b : Multisegment.{uV, uF} T} (h : RankLE b a) (hne : b ≠ a) :
    rankMeasure a.cuspidalContent a < rankMeasure a.cuspidalContent b := by
  have hI : ∃ I, containmentCount I a < containmentCount I b := by
    by_contra hcon
    push Not at hcon
    exact hne (h.antisymm ⟨h.1.symm, hcon⟩)
  obtain ⟨I, hlt⟩ := hI
  have hmem : I ∈ candidateSegments a.cuspidalContent := by
    obtain ⟨Δ, hΔ, hsub⟩ := (containmentCount_pos_iff I b).mp (by omega)
    rw [← h.1]
    exact mem_candidateSegments hΔ hsub
  exact Finset.sum_lt_sum (fun J _ => h.2 J) ⟨I, hmem, hlt⟩

/-- The strict rank order is well founded. -/
theorem wellFounded_rankLT :
    WellFounded fun b a : Multisegment.{uV, uF} T => RankLE b a ∧ b ≠ a := by
  let f : Multisegment.{uV, uF} T → ℕ := fun a =>
    (candidateSegments a.cuspidalContent).card * Multiset.card a.cuspidalContent -
      rankMeasure a.cuspidalContent a
  refine Subrelation.wf (r := InvImage (· < ·) f) ?_ (InvImage.wf f wellFounded_lt)
  intro b a ⟨h, hne⟩
  have hlt := rankMeasure_lt h hne
  have hb := rankMeasure_le b
  rw [h.1] at hb
  change _ - rankMeasure b.cuspidalContent b < _ - _
  rw [h.1]
  omega

theorem RankLE.degree_eq {a b : Multisegment.{uV, uF} T} (h : RankLE b a) :
    b.degree = a.degree := by
  rw [← sum_rank_cuspidalContent, ← sum_rank_cuspidalContent, h.1]

end Multisegment

end Langlands.PadicField.TopologicalData
