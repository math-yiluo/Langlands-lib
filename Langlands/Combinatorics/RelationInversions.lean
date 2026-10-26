import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.Pairwise
import Lean.Elab.Tactic.Omega

/-! # Counting inversions of a relation on a list

These elementary counts retain all occurrences. They isolate the numerical
part of the minimization argument in Zelevinsky (1980), Section 6.7.
-/

namespace Langlands.Combinatorics

universe u

variable {α : Type u} (R : α → α → Prop) [DecidableRel R]

/-- The number of related pairs, with the first entry in `l` and second in `r`.
Both lists are counted with their multiplicities. -/
def relationPairCount (l r : List α) : ℕ :=
  (l.map fun a => (r.map fun b => if R a b then 1 else 0).sum).sum

@[simp] theorem relationPairCount_nil_left (r : List α) :
    relationPairCount R [] r = 0 := rfl

@[simp] theorem relationPairCount_nil_right (l : List α) :
    relationPairCount R l [] = 0 := by
  simp [relationPairCount]

@[simp] theorem relationPairCount_cons_left (a : α) (l r : List α) :
    relationPairCount R (a :: l) r =
      (r.map fun b => if R a b then 1 else 0).sum + relationPairCount R l r := by
  simp [relationPairCount]

@[simp] theorem relationPairCount_cons_right (l : List α) (a : α) (r : List α) :
    relationPairCount R l (a :: r) =
      (l.map fun b => if R b a then 1 else 0).sum + relationPairCount R l r := by
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [relationPairCount_cons_left, ih]
    simp only [relationPairCount, List.map_cons, List.sum_cons]
    omega

@[simp] theorem relationPairCount_singletons (a b : α) :
    relationPairCount R [a] [b] = if R a b then 1 else 0 := by
  simp [relationPairCount]

@[simp] theorem relationPairCount_append_left (l m r : List α) :
    relationPairCount R (l ++ m) r =
      relationPairCount R l r + relationPairCount R m r := by
  simp [relationPairCount]

@[simp] theorem relationPairCount_append_right (l m r : List α) :
    relationPairCount R l (m ++ r) =
      relationPairCount R l m + relationPairCount R l r := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [relationPairCount_cons_left, ih]
    simp only [relationPairCount, List.map_append, List.sum_append]
    omega

/-- Count the pairs of positions `i < j` whose entries satisfy `R`.
No transitivity, asymmetry or distinctness is assumed. -/
def relationInversions : List α → ℕ
  | [] => 0
  | a :: l => relationPairCount R [a] l + relationInversions l

@[simp] theorem relationInversions_nil : relationInversions R [] = 0 := rfl

@[simp] theorem relationInversions_cons (a : α) (l : List α) :
    relationInversions R (a :: l) =
      relationPairCount R [a] l + relationInversions R l := rfl

@[simp] theorem relationInversions_singleton (a : α) :
    relationInversions R [a] = 0 := by simp

/-- Inversions in a concatenation consist of the two internal counts and
all related pairs crossing from the first list to the second. -/
theorem relationInversions_append (l r : List α) :
    relationInversions R (l ++ r) =
      relationInversions R l + relationInversions R r + relationPairCount R l r := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.cons_append, relationInversions_cons,
      relationPairCount_append_right, relationPairCount_cons_left,
      relationPairCount_nil_left, ih]
    omega

theorem relationPairCount_singleton_eq_zero_iff (a : α) (l : List α) :
    relationPairCount R [a] l = 0 ↔ ∀ b ∈ l, ¬ R a b := by
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [relationPairCount_cons_right, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.add_zero, Nat.add_eq_zero_iff, ih, List.mem_cons, forall_eq_or_imp]
    by_cases h : R a b <;> simp [h]

/-- Having no inversions is exactly the pairwise nonrelation condition. -/
theorem relationInversions_eq_zero_iff (l : List α) :
    relationInversions R l = 0 ↔ l.Pairwise (fun a b => ¬ R a b) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [relationInversions_cons, Nat.add_eq_zero_iff,
      relationPairCount_singleton_eq_zero_iff, ih, List.pairwise_cons]

/-- The contributions of entries to the left of a replacement can be compared
one occurrence at a time. -/
theorem relationPairCount_mono_right (l m m' : List α)
    (h : ∀ a ∈ l, relationPairCount R [a] m' ≤ relationPairCount R [a] m) :
    relationPairCount R l m' ≤ relationPairCount R l m := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [relationPairCount_cons_left]
    have ha := h a List.mem_cons_self
    simpa only [relationPairCount, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Nat.add_zero] using
      Nat.add_le_add ha (ih fun b hb => h b (List.mem_cons_of_mem a hb))

/-- The contributions of entries to the right of a replacement can likewise
be compared one occurrence at a time. -/
theorem relationPairCount_mono_left (l l' r : List α)
    (h : ∀ b ∈ r, relationPairCount R l' [b] ≤ relationPairCount R l [b]) :
    relationPairCount R l' r ≤ relationPairCount R l r := by
  induction r with
  | nil => simp
  | cons b r ih =>
    simp only [relationPairCount_cons_right]
    have hb := h b List.mem_cons_self
    simpa only [relationPairCount, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Nat.add_zero] using
      Nat.add_le_add hb (ih fun c hc => h c (List.mem_cons_of_mem b hc))

/-- A replacement with fewer internal inversions and no increase in either
external contribution strictly lowers the full count, even if lengths differ. -/
theorem relationInversions_replace_lt (l m m' r : List α)
    (hm : relationInversions R m' < relationInversions R m)
    (hl : ∀ a ∈ l, relationPairCount R [a] m' ≤ relationPairCount R [a] m)
    (hr : ∀ b ∈ r, relationPairCount R m' [b] ≤ relationPairCount R m [b]) :
    relationInversions R (l ++ m' ++ r) < relationInversions R (l ++ m ++ r) := by
  have hl' := relationPairCount_mono_right R l m m' hl
  have hr' := relationPairCount_mono_left R m m' r hr
  simp only [relationInversions_append, relationPairCount_append_left]
  omega

/-- Swapping neighboring entries affects only their mutual contribution. -/
theorem relationInversions_adjacent_swap (l r : List α) (a b : α) :
    relationInversions R (l ++ b :: a :: r) + (if R a b then 1 else 0) =
      relationInversions R (l ++ a :: b :: r) + (if R b a then 1 else 0) := by
  have hc : relationPairCount R l (a :: b :: r) =
      relationPairCount R l (b :: a :: r) := by
    simp only [relationPairCount_cons_right]
    omega
  simp only [relationInversions_append, relationInversions_cons,
    relationPairCount_cons_right,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  omega

theorem relationInversions_swap_unrelated (l r : List α) (a b : α)
    (hab : ¬ R a b) (hba : ¬ R b a) :
    relationInversions R (l ++ b :: a :: r) =
      relationInversions R (l ++ a :: b :: r) := by
  simpa [hab, hba] using
    relationInversions_adjacent_swap R l r a b

theorem relationInversions_swap_related_lt (l r : List α) (a b : α)
    (hab : R a b) (hba : ¬ R b a) :
    relationInversions R (l ++ b :: a :: r) <
      relationInversions R (l ++ a :: b :: r) := by
  have h := relationInversions_adjacent_swap R l r a b
  simp [hab, hba] at h
  omega

end Langlands.Combinatorics
