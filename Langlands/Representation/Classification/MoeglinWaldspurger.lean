import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Multiset.Bind
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic

/-!
# The integer-line Moeglin–Waldspurger algorithm

This is the shortest-segment algorithm of Badulescu's paragraph “The algorithm”,
equivalently Moeglin–Waldspurger II.2. Multiplicities are retained throughout.
-/

namespace Langlands.MoeglinWaldspurger

/-- A nonempty closed integer interval. -/
@[ext]
structure Interval where
  beginning : ℤ
  ending : ℤ
  nonempty : beginning ≤ ending
  deriving DecidableEq, Repr

namespace Interval

/-- Order by ending, breaking ties by beginning. Descending order chooses
the greatest ending and then the shortest interval with that ending. -/
instance : LinearOrder Interval :=
  LinearOrder.lift' (fun I => toLex (I.ending, I.beginning)) (by
    intro I J h
    have h' : (I.ending, I.beginning) = (J.ending, J.beginning) := h
    exact Interval.ext (congrArg Prod.snd h') (congrArg Prod.fst h'))

/-- Number of integer points, including both endpoints. -/
def length (I : Interval) : ℕ := (I.ending - I.beginning).toNat + 1

theorem length_pos (I : Interval) : 0 < I.length := Nat.succ_pos _

/-- Each point occurs once. -/
def support (I : Interval) : Multiset ℤ :=
  (Multiset.range I.length).map fun (i : ℕ) => I.beginning + (i : ℤ)

/-- Shorten at the right end, discarding a one-point interval. -/
def dropLast (I : Interval) : Multiset Interval :=
  if h : I.beginning < I.ending then
    {⟨I.beginning, I.ending - 1, by omega⟩}
  else 0

end Interval

/-- A finite multiset of nonempty integer intervals, including the empty input. -/
abbrev Multisegment := Multiset Interval

def beginnings (a : Multisegment) : Multiset ℤ := a.map Interval.beginning

def endings (a : Multisegment) : Multiset ℤ := a.map Interval.ending

/-- Multiset union of the interval supports, retaining repeated points. -/
def support (a : Multisegment) : Multiset ℤ := a.bind Interval.support

/-- Total number of points with multiplicity; the recursion measure. -/
def weight (a : Multisegment) : ℕ := (a.map Interval.length).sum

@[simp] theorem weight_zero : weight 0 = 0 := rfl

@[simp] theorem weight_cons (I : Interval) (a : Multisegment) :
    weight (I ::ₘ a) = I.length + weight a := by simp [weight]

@[simp] theorem weight_add (a b : Multisegment) :
    weight (a + b) = weight a + weight b := by simp [weight]

/-- Shorten each occurrence once. Only the selected multiset is passed here. -/
def shorten (a : Multisegment) : Multisegment := a.bind Interval.dropLast

theorem weight_shorten_add_card (a : Multisegment) :
    weight (shorten a) + a.card = weight a := by
  induction a using Multiset.induction_on with
  | empty => simp [shorten]
  | cons I a ih =>
    have hI : weight I.dropLast + 1 = I.length := by
      rcases I with ⟨b, e, hbe⟩
      simp only [Interval.dropLast, Interval.length]
      split_ifs <;> simp [weight, Interval.length] <;> omega
    simp only [shorten, Multiset.cons_bind, weight_add, Multiset.card_cons,
      weight_cons] at *
    omega

/-- A shortest interval ending at `e` which is not contained in the previous
interval, whose beginning is `previousBeginning` and whose end is `e+1`.
For these endpoints, noncontainment is exactly a strictly smaller beginning. -/
def pick (a : Multisegment) (e previousBeginning : ℤ) : Option Interval :=
  ((a.filter fun I => I.ending = e ∧ I.beginning < previousBeginning).sort
    (fun I J => J ≤ I)).head?

theorem pick_mem {a : Multisegment} {e b : ℤ} {I : Interval}
    (h : pick a e b = some I) : I ∈ a := by
  have hm := List.mem_of_mem_head? h
  have hf := (Multiset.mem_sort (fun I J : Interval => J ≤ I)).mp hm
  exact (Multiset.mem_filter.mp hf).1

theorem pick_spec {a : Multisegment} {e b : ℤ} {I : Interval}
    (h : pick a e b = some I) : I.ending = e ∧ I.beginning < b := by
  have hm := List.mem_of_mem_head? h
  have hf := (Multiset.mem_sort (fun I J : Interval => J ≤ I)).mp hm
  exact (Multiset.mem_filter.mp hf).2

/-- Select successive intervals, erasing one occurrence of each selection.
The result is the ordered selected list and the untouched remainder. -/
def chain (a : Multisegment) (e previousBeginning : ℤ) :
    List Interval × Multisegment :=
  match h : pick a e previousBeginning with
  | none => ([], a)
  | some I =>
    let next := chain (a.erase I) (e - 1) I.beginning
    (I :: next.1, next.2)
termination_by a.card
decreasing_by exact Multiset.card_erase_lt_of_mem (pick_mem h)

theorem chain_partition (a : Multisegment) (e b : ℤ) :
    ((chain a e b).1 : Multisegment) + (chain a e b).2 = a := by
  induction a using (measure (fun a : Multisegment => a.card)).wf.induction
      generalizing e b with
  | h a ih =>
    rw [chain]
    split
    · simp
    · rename_i I hp
      dsimp only
      rw [← Multiset.cons_coe, Multiset.cons_add, ih (a.erase I)
        (Multiset.card_erase_lt_of_mem (pick_mem hp)),
        Multiset.cons_erase (pick_mem hp)]

theorem chain_beginnings_lt (a : Multisegment) (e b : ℤ) :
    ∀ I ∈ (chain a e b).1, I.beginning < b := by
  induction a using (measure (fun a : Multisegment => a.card)).wf.induction
      generalizing e b with
  | h a ih =>
    rw [chain]
    split
    · simp
    · rename_i I hp
      simp only [List.mem_cons]
      intro J hJ
      rcases hJ with rfl | hJ
      · exact (pick_spec hp).2
      · exact lt_trans
          (ih (a.erase I) (Multiset.card_erase_lt_of_mem (pick_mem hp)) _ _ J hJ)
          (pick_spec hp).2

theorem chain_decreasing (a : Multisegment) (e b : ℤ) :
    (chain a e b).1.Pairwise (fun I J => J.beginning < I.beginning) := by
  induction a using (measure (fun a : Multisegment => a.card)).wf.induction
      generalizing e b with
  | h a ih =>
    rw [chain]
    split
    · simp
    · rename_i I hp
      exact List.pairwise_cons.mpr
        ⟨chain_beginnings_lt _ _ _, ih _ (Multiset.card_erase_lt_of_mem (pick_mem hp)) _ _⟩

theorem chain_ending (a : Multisegment) (e b : ℤ)
    (i : ℕ) (hi : i < (chain a e b).1.length) :
    ((chain a e b).1[i]).ending = e - (i : ℤ) := by
  induction a using (measure (fun a : Multisegment => a.card)).wf.induction
      generalizing e b i with
  | h a ih =>
    generalize hc : chain a e b = result at hi ⊢
    rw [chain] at hc
    split at hc
    · subst result
      simp at hi
    · rename_i I hp
      subst result
      dsimp only at hi ⊢
      cases i with
      | zero => simpa using (pick_spec hp).1
      | succ i =>
        have hi' : i < (chain (a.erase I) (e - 1) I.beginning).1.length := by
          simpa using hi
        have hrec := ih _ (Multiset.card_erase_lt_of_mem (pick_mem hp)) _ _ i hi'
        simpa only [Prod.fst, List.getElem_cons_succ] using
          hrec.trans (by push_cast; ring)

/-- The raw data of a nonempty round. The first interval has the greatest
ending; the rest are obtained by `chain`. No mathematical correctness
properties are fields of this structure. -/
structure Round where
  first : Interval
  tail : List Interval
  untouched : Multisegment

namespace Round

def selectedList (r : Round) : List Interval := r.first :: r.tail

def selected (r : Round) : Multisegment := r.selectedList

/-- If the chain has `r+1` selections ending at `e,...,e-r`, emit `[e-r,e]`. -/
def emitted (r : Round) : Interval :=
  ⟨r.first.ending - (r.tail.length : ℤ), r.first.ending, by omega⟩

def residual (r : Round) : Multisegment := r.untouched + shorten r.selected

end Round

/-- Sort canonically to choose the greatest ending and a shortest first interval.
Equal intervals remain repeated occurrences. -/
def round (a : Multisegment) : Option Round :=
  match a.sort (fun I J => J ≤ I) with
  | [] => none
  | I :: l =>
    let next := chain (l : Multisegment) (I.ending - 1) I.beginning
    some ⟨I, next.1, next.2⟩

theorem round_none_iff (a : Multisegment) : round a = none ↔ a = 0 := by
  unfold round
  cases hs : a.sort (fun I J => J ≤ I) with
  | nil =>
    have ha : a = 0 := by
      have := Multiset.sort_eq a (fun I J => J ≤ I)
      simpa [hs] using this.symm
    simp [ha]
  | cons I l =>
    have ha : a ≠ 0 := by
      intro ha
      simp [ha] at hs
    simp [ha]

theorem round_partition {a : Multisegment} {r : Round} (h : round a = some r) :
    r.selected + r.untouched = a := by
  unfold round at h
  cases hs : a.sort (fun I J => J ≤ I) with
  | nil => simp [hs] at h
  | cons I l =>
    simp only [hs, Option.some.injEq] at h
    subst r
    change (I ::ₘ ((chain (l : Multisegment) _ _).1 : Multisegment)) +
      (chain (l : Multisegment) _ _).2 = a
    rw [Multiset.cons_add, chain_partition]
    have := Multiset.sort_eq a (fun I J => J ≤ I)
    simpa [hs] using this

theorem round_decreasing {a : Multisegment} {r : Round} (h : round a = some r) :
    r.selectedList.Pairwise (fun I J => J.beginning < I.beginning) := by
  unfold round at h
  cases hs : a.sort (fun I J => J ≤ I) with
  | nil => simp [hs] at h
  | cons I l =>
    simp only [hs, Option.some.injEq] at h
    subst r
    exact List.pairwise_cons.mpr ⟨chain_beginnings_lt _ _ _, chain_decreasing _ _ _⟩

theorem round_ending {a : Multisegment} {r : Round} (h : round a = some r)
    (i : ℕ) (hi : i < r.selectedList.length) :
    (r.selectedList[i]).ending = r.first.ending - (i : ℤ) := by
  unfold round at h
  cases hs : a.sort (fun I J => J ≤ I) with
  | nil => simp [hs] at h
  | cons I l =>
    simp only [hs, Option.some.injEq] at h
    subst r
    cases i with
    | zero => simp [Round.selectedList]
    | succ i =>
      have hi' : i < (chain (l : Multisegment) (I.ending - 1) I.beginning).1.length := by
        simpa [Round.selectedList] using hi
      have hrec := chain_ending (l : Multisegment) (I.ending - 1) I.beginning i hi'
      simpa only [Round.selectedList, List.getElem_cons_succ] using
        hrec.trans (by push_cast; ring)

theorem round_weight_lt {a : Multisegment} {r : Round} (h : round a = some r) :
    weight r.residual < weight a := by
  have hp := congrArg weight (round_partition h)
  rw [weight_add] at hp
  have hs := weight_shorten_add_card r.selected
  have hc : 0 < r.selected.card := by simp [Round.selected, Round.selectedList]
  simp only [Round.residual, weight_add]
  omega

/-- The actual recursive Moeglin–Waldspurger output. Every nonempty round emits
one interval and recurses on the precisely shortened selected occurrences.
The proved strict decrease of support weight makes this a total definition. -/
def dual (a : Multisegment) : Multisegment :=
  match h : round a with
  | none => 0
  | some r => r.emitted ::ₘ dual r.residual
termination_by weight a
decreasing_by exact round_weight_lt h

@[simp] theorem dual_zero : dual 0 = 0 := by
  rw [dual, (round_none_iff 0).2 rfl]

theorem dual_of_round {a : Multisegment} {r : Round} (h : round a = some r) :
    dual a = r.emitted ::ₘ dual r.residual := by rw [dual, h]

end Langlands.MoeglinWaldspurger
