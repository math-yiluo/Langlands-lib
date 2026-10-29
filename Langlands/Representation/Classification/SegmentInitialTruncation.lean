import Langlands.Representation.Classification.Segments

/-! # One-step initial segment truncation -/

namespace Langlands.PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

namespace Segment

/-- Delete the final position of a segment of length greater than one. -/
def dropLastNonempty (Δ : Segment.{uV, uF} T) (h : 1 < Δ.length) :
    Segment.{uV, uF} T where
  base := Δ.base
  length := Δ.length - 1
  length_pos := by omega

@[simp]
theorem dropLastNonempty_base (Δ : Segment.{uV, uF} T) (h : 1 < Δ.length) :
    (Δ.dropLastNonempty h).base = Δ.base := rfl

@[simp]
theorem dropLastNonempty_length (Δ : Segment.{uV, uF} T) (h : 1 < Δ.length) :
    (Δ.dropLastNonempty h).length = Δ.length - 1 := rfl

@[simp]
theorem dropLastNonempty_rank (Δ : Segment.{uV, uF} T) (h : 1 < Δ.length) :
    (Δ.dropLastNonempty h).rank = Δ.rank := rfl

@[simp]
theorem dropLastNonempty_member (Δ : Segment.{uV, uF} T) (h : 1 < Δ.length)
    (i : ℕ) : (Δ.dropLastNonempty h).member i = Δ.member i := rfl

/-- The nonempty truncation has degree `(m - 1) r`. -/
theorem dropLastNonempty_degree_add_rank (Δ : Segment.{uV, uF} T) (h : 1 < Δ.length) :
    (Δ.dropLastNonempty h).degree + Δ.rank = Δ.degree := by
  change (Δ.length - 1) * Δ.rank + Δ.rank = Δ.length * Δ.rank
  simpa only [Nat.add_mul, Nat.one_mul] using
    congrArg (fun m : ℕ => m * Δ.rank) (Nat.sub_add_cancel (by omega : 1 ≤ Δ.length))

/-- Zelevinsky's `Δ⁻`: `none` for a singleton, and deletion of the last
position otherwise. The empty outcome is not a length-zero segment. -/
def dropLast (Δ : Segment.{uV, uF} T) : Option (Segment.{uV, uF} T) :=
  if h : 1 < Δ.length then some (Δ.dropLastNonempty h) else none

theorem dropLast_of_one_lt (Δ : Segment.{uV, uF} T) (h : 1 < Δ.length) :
    Δ.dropLast = some (Δ.dropLastNonempty h) := by
  simp [dropLast, h]

@[simp]
theorem dropLast_eq_none_iff (Δ : Segment.{uV, uF} T) :
    Δ.dropLast = none ↔ Δ.length = 1 := by
  have := Δ.length_pos
  simp only [dropLast]
  split_ifs <;> simp_all <;> omega

theorem dropLast_of_length_eq_one (Δ : Segment.{uV, uF} T) (h : Δ.length = 1) :
    Δ.dropLast = none := (dropLast_eq_none_iff Δ).mpr h

/-- Truncation removes exactly one copy of the common cuspidal rank. -/
theorem dropLast_degree_add_rank (Δ : Segment.{uV, uF} T) :
    ((Δ.dropLast.map degree).getD 0) + Δ.rank = Δ.degree := by
  by_cases h : 1 < Δ.length
  · rw [Δ.dropLast_of_one_lt h]
    exact Δ.dropLastNonempty_degree_add_rank h
  · have hlen : Δ.length = 1 := by have := Δ.length_pos; omega
    rw [Δ.dropLast_of_length_eq_one hlen]
    simp [degree, hlen]

/-- Apply `Δ ↦ Δ⁻` in the supplied list order and omit empty outcomes.
Repeated surviving terms remain repeated. -/
def dropLastList (l : List (Segment.{uV, uF} T)) : List (Segment.{uV, uF} T) :=
  l.filterMap dropLast

@[simp]
theorem dropLastList_nil : dropLastList ([] : List (Segment.{uV, uF} T)) = [] := rfl

theorem dropLastList_cons (Δ : Segment.{uV, uF} T) (l : List (Segment.{uV, uF} T)) :
    dropLastList (Δ :: l) =
      match Δ.dropLast with
      | none => dropLastList l
      | some Γ => Γ :: dropLastList l := by
  cases h : Δ.dropLast <;> simp [dropLastList, h]

theorem dropLastList_cons_of_one_lt (Δ : Segment.{uV, uF} T) (h : 1 < Δ.length)
    (l : List (Segment.{uV, uF} T)) :
    dropLastList (Δ :: l) = Δ.dropLastNonempty h :: dropLastList l := by
  simp [dropLastList, Δ.dropLast_of_one_lt h]

theorem dropLastList_cons_of_length_eq_one (Δ : Segment.{uV, uF} T) (h : Δ.length = 1)
    (l : List (Segment.{uV, uF} T)) :
    dropLastList (Δ :: l) = dropLastList l := by
  simp [dropLastList, Δ.dropLast_of_length_eq_one h]

theorem dropLastList_append (l₁ l₂ : List (Segment.{uV, uF} T)) :
    dropLastList (l₁ ++ l₂) = dropLastList l₁ ++ dropLastList l₂ :=
  List.filterMap_append

theorem mem_dropLastList {Γ : Segment.{uV, uF} T} {l : List (Segment.{uV, uF} T)} :
    Γ ∈ dropLastList l ↔ ∃ Δ ∈ l, Δ.dropLast = some Γ :=
  List.mem_filterMap

/-- Summed over a list, truncation removes one cuspidal rank from each term. -/
theorem dropLastList_degree_add_rank (l : List (Segment.{uV, uF} T)) :
    ((dropLastList l).map degree).sum + (l.map rank).sum = (l.map degree).sum := by
  induction l with
  | nil => rfl
  | cons Δ l ih =>
    have hΔ := Δ.dropLast_degree_add_rank
    rw [dropLastList_cons]
    cases h : Δ.dropLast with
    | none =>
      rw [h, Option.map_none, Option.getD_none] at hΔ
      simp only [List.map_cons, List.sum_cons]
      omega
    | some Γ =>
      rw [h, Option.map_some, Option.getD_some] at hΔ
      simp only [List.map_cons, List.sum_cons]
      omega

end Segment

end Langlands.PadicField.TopologicalData
