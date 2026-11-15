import Langlands.Representation.Classification.MoeglinWaldspurgerRealization
import Langlands.Representation.Classification.TadicMultisegments
import Langlands.Representation.Aubert.MultisegmentRankOrder

/-! # The MW recursion on integer rectangles -/

namespace Langlands.MoeglinWaldspurger

/-- Row `i` of an integer rectangle with base `b` and rows of `m + 1` points:
the interval `[b + i, b + i + m]`. -/
def rectangleRow (b : ℤ) (m i : ℕ) : Interval :=
  ⟨b + (i : ℤ), b + (i : ℤ) + (m : ℤ), by omega⟩

/-- The `n + 1` rows `[b + i, b + i + m]`, `0 ≤ i ≤ n`, each with `m + 1` points. -/
def rectangle (b : ℤ) (n m : ℕ) : Multisegment :=
  (Multiset.range (n + 1)).map (rectangleRow b m)

theorem rectangleRow_le_of_le (b : ℤ) (m : ℕ) {i j : ℕ} (h : i ≤ j) :
    rectangleRow b m i ≤ rectangleRow b m j := by
  change toLex ((rectangleRow b m i).ending, (rectangleRow b m i).beginning) ≤
    toLex ((rectangleRow b m j).ending, (rectangleRow b m j).beginning)
  rcases Nat.lt_or_eq_of_le h with h | rfl
  · exact le_of_lt (Prod.Lex.toLex_strictMono (Prod.mk_lt_mk_of_lt_of_le
      (by simp only [rectangleRow]; omega) (by simp only [rectangleRow]; omega)))
  · exact le_rfl

/-- Descending sorting lists the rows from the top row down. -/
theorem sort_rows (b : ℤ) (m : ℕ) (j : ℕ) :
    ((Multiset.range j).map (rectangleRow b m)).sort (fun I J => J ≤ I) =
      (List.range j).reverse.map (rectangleRow b m) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Multiset.range_succ, Multiset.map_cons, Multiset.sort_cons, ih]
    · simp [List.range_succ]
    · intro J hJ
      obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hJ
      exact rectangleRow_le_of_le b m (Multiset.mem_range.mp hi).le

/-- In the rows `0, ..., j - 1`, the top row is the only admissible pick. -/
theorem pick_rows (b : ℤ) (m j : ℕ) :
    pick ((Multiset.range (j + 1)).map (rectangleRow b m))
      (b + (j : ℤ) + (m : ℤ)) (b + (j : ℤ) + 1) = some (rectangleRow b m j) := by
  have hf : ((Multiset.range (j + 1)).map (rectangleRow b m)).filter
      (fun I => I.ending = b + (j : ℤ) + (m : ℤ) ∧ I.beginning < b + (j : ℤ) + 1) =
      {rectangleRow b m j} := by
    rw [Multiset.range_succ, Multiset.map_cons, Multiset.filter_cons_of_pos]
    · rw [Multiset.filter_eq_nil.mpr]
      · rfl
      · intro J hJ
        obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hJ
        have := Multiset.mem_range.mp hi
        simp only [rectangleRow, not_and]
        omega
    · exact ⟨rfl, by simp [rectangleRow]⟩
  unfold pick
  rw [hf, Multiset.sort_singleton]
  rfl

/-- The chain below the top row selects every remaining row, in descending order. -/
theorem chain_rows (b : ℤ) (m : ℕ) (j : ℕ) :
    chain ((Multiset.range j).map (rectangleRow b m))
        (b + (j : ℤ) - 1 + (m : ℤ)) (b + (j : ℤ)) =
      ((List.range j).reverse.map (rectangleRow b m), 0) := by
  induction j with
  | zero =>
    rw [chain]
    split
    · simp
    · rename_i I hp
      simp [pick] at hp
  | succ j ih =>
    have hp := pick_rows b m j
    rw [chain]
    split
    · rename_i hn
      have : b + ((j + 1 : ℕ) : ℤ) - 1 + (m : ℤ) = b + (j : ℤ) + (m : ℤ) := by push_cast; ring
      rw [this, show b + ((j + 1 : ℕ) : ℤ) = b + (j : ℤ) + 1 by push_cast; ring, hp] at hn
      cases hn
    · rename_i I hI
      have : b + ((j + 1 : ℕ) : ℤ) - 1 + (m : ℤ) = b + (j : ℤ) + (m : ℤ) := by push_cast; ring
      rw [this, show b + ((j + 1 : ℕ) : ℤ) = b + (j : ℤ) + 1 by push_cast; ring, hp] at hI
      cases hI
      have he : ((Multiset.range (j + 1)).map (rectangleRow b m)).erase (rectangleRow b m j) =
          (Multiset.range j).map (rectangleRow b m) := by
        rw [Multiset.range_succ, Multiset.map_cons, Multiset.erase_cons_head]
      have hb : (rectangleRow b m j).beginning = b + (j : ℤ) := rfl
      have he' : b + ((j + 1 : ℕ) : ℤ) - 1 + (m : ℤ) - 1 = b + (j : ℤ) - 1 + (m : ℤ) := by
        push_cast; ring
      simp only [he, hb, he', ih, List.range_succ, List.reverse_append,
        List.reverse_cons, List.reverse_nil, List.nil_append, List.map_cons, List.cons_append]

/-- One MW round on a rectangle selects every row. -/
theorem round_rectangle (b : ℤ) (n m : ℕ) :
    round (rectangle b n m) =
      some ⟨rectangleRow b m n, (List.range n).reverse.map (rectangleRow b m), 0⟩ := by
  unfold round
  rw [rectangle, sort_rows]
  simp only [List.range_succ, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.map_cons, List.cons_append]
  have hc := chain_rows b m n
  have hl : (((List.range n).reverse.map (rectangleRow b m) : List Interval) : Multisegment) =
      (Multiset.range n).map (rectangleRow b m) := by
    rw [← Multiset.map_coe, Multiset.coe_reverse]
    rfl
  have he : (rectangleRow b m n).ending - 1 = b + (n : ℤ) - 1 + (m : ℤ) := by
    simp only [rectangleRow]; ring
  have hb : (rectangleRow b m n).beginning = b + (n : ℤ) := rfl
  rw [hl, he, hb, hc]

theorem dropLast_rectangleRow_succ (b : ℤ) (m i : ℕ) :
    (rectangleRow b (m + 1) i).dropLast = {rectangleRow b m i} := by
  unfold Interval.dropLast
  rw [dite_eq_left_of_eq_true (eq_true (by simp only [rectangleRow]; omega))]
  congr 1
  ext
  · simp [rectangleRow]
  · simp only [rectangleRow]; push_cast; ring

theorem dropLast_rectangleRow_zero (b : ℤ) (i : ℕ) :
    (rectangleRow b 0 i).dropLast = 0 := by
  unfold Interval.dropLast
  rw [dite_eq_right_of_eq_false (eq_false (by simp only [rectangleRow]; omega))]

/-- The selected occurrences of the rectangle round are all rows. -/
theorem selected_rectangle (b : ℤ) (n m : ℕ) :
    (⟨rectangleRow b m n, (List.range n).reverse.map (rectangleRow b m), 0⟩ : Round).selected =
      rectangle b n m := by
  simp only [Round.selected, Round.selectedList, rectangle, Multiset.range_succ,
    Multiset.map_cons]
  rw [← Multiset.cons_coe, ← Multiset.map_coe, Multiset.coe_reverse]
  rfl

/-- The emitted interval of the rectangle round is the last transposed row. -/
theorem emitted_rectangle (b : ℤ) (n m : ℕ) :
    (⟨rectangleRow b m n, (List.range n).reverse.map (rectangleRow b m), 0⟩ : Round).emitted =
      rectangleRow b n m := by
  simp only [Round.emitted, rectangleRow, List.length_map, List.length_reverse,
    List.length_range]
  ext <;> simp only <;> ring

/-- The MW dual of an integer rectangle is its transpose. -/
theorem dual_rectangle (b : ℤ) (n m : ℕ) :
    dual (rectangle b n m) = rectangle b m n := by
  induction m with
  | zero =>
    rw [dual_of_round (round_rectangle b n 0), emitted_rectangle]
    have hres : Round.residual ⟨rectangleRow b 0 n,
        (List.range n).reverse.map (rectangleRow b 0), 0⟩ = 0 := by
      rw [Round.residual, selected_rectangle, zero_add, shorten, rectangle,
        Multiset.bind_map]
      simp only [dropLast_rectangleRow_zero, Multiset.bind_zero]
    rw [hres, dual_zero]
    rfl
  | succ m ih =>
    rw [dual_of_round (round_rectangle b n (m + 1)), emitted_rectangle]
    have hres : Round.residual ⟨rectangleRow b (m + 1) n,
        (List.range n).reverse.map (rectangleRow b (m + 1)), 0⟩ = rectangle b n m := by
      rw [Round.residual, selected_rectangle, zero_add, shorten, rectangle,
        Multiset.bind_map]
      simp only [dropLast_rectangleRow_succ, Multiset.bind_singleton]
      rfl
    rw [hres, ih, rectangle, rectangle, Multiset.range_succ (m + 1), Multiset.map_cons]

section Realization

open PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- An integer rectangle realized at the centering offset is Tadić's `a(n + 1, m + 1)^ρ`. -/
theorem realize_rectangle (ρ : T.CuspidalDatum.{uV, uF}) (b : ℤ) (n m : ℕ) (x : ℝ)
    (hx : x + (b : ℝ) = -((n : ℝ) + m) / 2) :
    realize ρ x (rectangle b n m) =
      Classification.tadicMultisegment ρ (n + 1) (m + 1) (Nat.succ_pos m) := by
  unfold realize rectangle Classification.tadicMultisegment
  rw [Multiset.map_map]
  apply Multiset.map_congr rfl
  intro i _
  apply Segment.ext_base_length
  · simp only [Function.comp_apply, Interval.realize_base, rectangleRow,
      Classification.tadicCenteredSegment]
    congr 1
    push_cast
    linarith
  · simp only [Function.comp_apply, Interval.realize_length, rectangleRow, Interval.length,
      Classification.tadicCenteredSegment_length]
    omega

end Realization

end Langlands.MoeglinWaldspurger
