import Langlands.Representation.Aubert.MultisegmentRankOrder

/-!
# Beginning and ending bounds in the multisegment rank order

Internal combinatorial adapters for the endpoint bounds in Badulescu's
neighboring Speh product argument.
-/

noncomputable section

namespace Langlands.PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

open scoped Classical

namespace Segment

/-- The adjacent two-member segment starting at `ρ`. -/
def adjacentPair (ρ : CuspidalDatum.{uV, uF} T) : Segment.{uV, uF} T :=
  ⟨ρ, 2, by omega⟩

/-- The adjacent two-member segment ending at `ρ`. -/
def precedingPair (ρ : CuspidalDatum.{uV, uF} T) : Segment.{uV, uF} T :=
  adjacentPair (ρ.twist (-1))

@[simp]
theorem precedingPair_last (ρ : CuspidalDatum.{uV, uF} T) :
    (precedingPair ρ).last = ρ := by
  simp [precedingPair, adjacentPair, last, member, CuspidalDatum.twist_twist]

theorem mem_support_iff_last_or_adjacentPair (ρ : CuspidalDatum.{uV, uF} T)
    (Δ : Segment.{uV, uF} T) :
    ρ ∈ Δ.support ↔ Δ.last = ρ ∨ (adjacentPair ρ).support ⊆ Δ.support := by
  constructor
  · rintro ⟨i, hi, hρ⟩
    by_cases he : i = Δ.length - 1
    · exact Or.inl (by simpa only [last, he] using hρ)
    · right
      apply support_subset_iff.mpr
      exact ⟨i, hρ.symm, by change i + 2 ≤ Δ.length; omega⟩
  · rintro (he | hp)
    · exact he ▸ Δ.last_mem_support
    · exact hp (adjacentPair ρ).base_mem_support

theorem not_adjacentPair_subset_of_last_eq {ρ : CuspidalDatum.{uV, uF} T}
    {Δ : Segment.{uV, uF} T} (h : Δ.last = ρ) :
    ¬ (adjacentPair ρ).support ⊆ Δ.support := by
  rintro hp
  obtain ⟨i, hi, hlen⟩ := support_subset_iff.mp hp
  have he : Δ.member (Δ.length - 1) = Δ.member i := h.trans hi
  have heq := Δ.member_injective he
  change i + 2 ≤ Δ.length at hlen
  have := Δ.length_pos
  omega

theorem mem_support_iff_base_or_precedingPair (ρ : CuspidalDatum.{uV, uF} T)
    (Δ : Segment.{uV, uF} T) :
    ρ ∈ Δ.support ↔ Δ.base = ρ ∨ (precedingPair ρ).support ⊆ Δ.support := by
  constructor
  · rintro ⟨i, hi, hρ⟩
    by_cases hb : i = 0
    · exact Or.inl (by simpa only [hb, member_zero] using hρ)
    · right
      apply support_subset_iff.mpr
      refine ⟨i - 1, ?_, by change i - 1 + 2 ≤ Δ.length; omega⟩
      change ρ.twist (-1) = Δ.member (i - 1)
      rw [← hρ]
      simp only [member, CuspidalDatum.twist_twist]
      congr 1
      rw [Nat.cast_sub (by omega : 1 ≤ i)]
      norm_num
      ring
  · rintro (hb | hp)
    · exact hb ▸ Δ.base_mem_support
    · exact hp (by simpa only [precedingPair_last] using
        (precedingPair ρ).last_mem_support)

theorem not_precedingPair_subset_of_base_eq {ρ : CuspidalDatum.{uV, uF} T}
    {Δ : Segment.{uV, uF} T} (h : Δ.base = ρ) :
    ¬ (precedingPair ρ).support ⊆ Δ.support := by
  rintro hp
  obtain ⟨i, hi, -⟩ := support_subset_iff.mp hp
  have he : Δ.member 0 = Δ.member (i + 1) := by
    calc
      Δ.member 0 = ρ := Δ.member_zero.trans h
      _ = ((precedingPair ρ).base).twist (1 : ℝ) := by
        simp [precedingPair, adjacentPair, CuspidalDatum.twist_twist]
      _ = (Δ.member i).twist (1 : ℝ) := congrArg (fun x => x.twist (1 : ℝ)) hi
      _ = Δ.member (i + 1) := by simpa only [Nat.cast_one] using Δ.member_twist_natCast i 1
  have := Δ.member_injective he
  omega

end Segment

namespace Multisegment

open Segment

/-- Endings of segment occurrences, retaining multiplicity. -/
def endings (a : Multisegment.{uV, uF} T) : Multiset (CuspidalDatum.{uV, uF} T) :=
  a.map Segment.last

/-- Beginnings of segment occurrences, retaining multiplicity. -/
def beginnings (a : Multisegment.{uV, uF} T) : Multiset (CuspidalDatum.{uV, uF} T) :=
  a.map Segment.base

/-- At `ρ`, support multiplicity is the sum of ending multiplicity and the
number of segments that continue to the next member. -/
theorem content_count_eq_endings_add_containment (ρ : CuspidalDatum.{uV, uF} T)
    (a : Multisegment.{uV, uF} T) :
    a.cuspidalContent.count ρ =
      (endings a).count ρ + containmentCount (adjacentPair ρ) a := by
  classical
  induction a using Multiset.induction_on with
  | empty => simp [endings, cuspidalContent]
  | cons Δ a ih =>
    rw [cuspidalContent_cons, Multiset.count_add, ih, containmentCount_cons]
    simp only [endings, Multiset.map_cons, Multiset.count_cons]
    by_cases he : Δ.last = ρ
    · have hmem : ρ ∈ Δ.cuspidalContent :=
        (Δ.mem_cuspidalContent ρ).mpr (he ▸ Δ.last_mem_support)
      rw [Multiset.count_eq_one_of_mem Δ.cuspidalContent_nodup hmem]
      simp only [he, not_adjacentPair_subset_of_last_eq he, ↓reduceIte]
      omega
    · by_cases hp : (adjacentPair ρ).support ⊆ Δ.support
      · have hmem : ρ ∈ Δ.cuspidalContent :=
          (Δ.mem_cuspidalContent ρ).mpr
            ((mem_support_iff_last_or_adjacentPair ρ Δ).mpr (Or.inr hp))
        rw [Multiset.count_eq_one_of_mem Δ.cuspidalContent_nodup hmem]
        simp only [Ne.symm he, hp, ↓reduceIte]
        omega
      · have hmem : ρ ∉ Δ.cuspidalContent := by
          rw [Δ.mem_cuspidalContent ρ, mem_support_iff_last_or_adjacentPair]
          exact not_or.mpr ⟨he, hp⟩
        rw [Multiset.count_eq_zero_of_notMem hmem]
        simp only [Ne.symm he, hp, ↓reduceIte]
        omega

/-- At `ρ`, support multiplicity is the sum of beginning multiplicity and the
number of segments that contain the preceding member as well. -/
theorem content_count_eq_beginnings_add_containment (ρ : CuspidalDatum.{uV, uF} T)
    (a : Multisegment.{uV, uF} T) :
    a.cuspidalContent.count ρ =
      (beginnings a).count ρ + containmentCount (precedingPair ρ) a := by
  classical
  induction a using Multiset.induction_on with
  | empty => simp [beginnings, cuspidalContent]
  | cons Δ a ih =>
    rw [cuspidalContent_cons, Multiset.count_add, ih, containmentCount_cons]
    simp only [beginnings, Multiset.map_cons, Multiset.count_cons]
    by_cases hb : Δ.base = ρ
    · have hmem : ρ ∈ Δ.cuspidalContent :=
        (Δ.mem_cuspidalContent ρ).mpr (hb ▸ Δ.base_mem_support)
      rw [Multiset.count_eq_one_of_mem Δ.cuspidalContent_nodup hmem]
      simp only [hb, not_precedingPair_subset_of_base_eq hb, ↓reduceIte]
      omega
    · by_cases hp : (precedingPair ρ).support ⊆ Δ.support
      · have hmem : ρ ∈ Δ.cuspidalContent :=
          (Δ.mem_cuspidalContent ρ).mpr
            ((mem_support_iff_base_or_precedingPair ρ Δ).mpr (Or.inr hp))
        rw [Multiset.count_eq_one_of_mem Δ.cuspidalContent_nodup hmem]
        simp only [Ne.symm hb, hp, ↓reduceIte]
        omega
      · have hmem : ρ ∉ Δ.cuspidalContent := by
          rw [Δ.mem_cuspidalContent ρ, mem_support_iff_base_or_precedingPair]
          exact not_or.mpr ⟨hb, hp⟩
        rw [Multiset.count_eq_zero_of_notMem hmem]
        simp only [Ne.symm hb, hp, ↓reduceIte]
        omega

/-- Rank-lowering can only remove ending occurrences. -/
theorem RankLE.endings_le {a b : Multisegment.{uV, uF} T} (h : RankLE b a) :
    endings b ≤ endings a := by
  classical
  apply Multiset.le_iff_count.mpr
  intro ρ
  have hc := congrArg (fun c => c.count ρ) h.1
  rw [content_count_eq_endings_add_containment,
    content_count_eq_endings_add_containment] at hc
  have hr := h.2 (adjacentPair ρ)
  omega

/-- Rank-lowering can only remove beginning occurrences. -/
theorem RankLE.beginnings_le {a b : Multisegment.{uV, uF} T} (h : RankLE b a) :
    beginnings b ≤ beginnings a := by
  classical
  apply Multiset.le_iff_count.mpr
  intro ρ
  have hc := congrArg (fun c => c.count ρ) h.1
  rw [content_count_eq_beginnings_add_containment,
    content_count_eq_beginnings_add_containment] at hc
  have hr := h.2 (precedingPair ρ)
  omega

end Multisegment

end Langlands.PadicField.TopologicalData
