import Langlands.Combinatorics.RelationInversions
import Mathlib.Data.List.Sort
import Mathlib.Logic.Relation
import Mathlib.Order.Extension.Linear
import Mathlib.Order.RelClasses

/-! # Exposing inversions by unrelated adjacent swaps

Acyclicity is an explicit hypothesis. The order extension used in the proof
is an auxiliary combinatorial order, not a representation-theoretic exponent.
-/

namespace Langlands.Combinatorics

universe u v

variable {α : Type u} (R : α → α → Prop)

/-- One adjacent swap for which neither direction of the relation holds. -/
def UnrelatedAdjacentSwap (l l' : List α) : Prop :=
  ∃ (s t : List α) (a b : α),
    l = s ++ a :: b :: t ∧ l' = s ++ b :: a :: t ∧ ¬ R a b ∧ ¬ R b a

/-- A finite sequence of unrelated adjacent swaps, including no swaps. -/
def UnrelatedSwapReachable : List α → List α → Prop :=
  Relation.ReflTransGen (UnrelatedAdjacentSwap R)

variable {R}

theorem UnrelatedAdjacentSwap.symm {l l' : List α}
    (h : UnrelatedAdjacentSwap R l l') : UnrelatedAdjacentSwap R l' l := by
  obtain ⟨s, t, a, b, rfl, rfl, hab, hba⟩ := h
  exact ⟨s, t, b, a, rfl, rfl, hba, hab⟩

theorem UnrelatedSwapReachable.refl (l : List α) : UnrelatedSwapReachable R l l :=
  Relation.ReflTransGen.refl

theorem UnrelatedSwapReachable.trans {l m n : List α}
    (h : UnrelatedSwapReachable R l m) (h' : UnrelatedSwapReachable R m n) :
    UnrelatedSwapReachable R l n :=
  Relation.ReflTransGen.trans h h'

theorem UnrelatedSwapReachable.swap (s t : List α) (a b : α)
    (hab : ¬ R a b) (hba : ¬ R b a) :
    UnrelatedSwapReachable R (s ++ a :: b :: t) (s ++ b :: a :: t) :=
  Relation.ReflTransGen.single ⟨s, t, a, b, rfl, rfl, hab, hba⟩

/-- Every invariant preserved by unrelated swaps is preserved by reachability. -/
theorem UnrelatedSwapReachable.preserves {P : List α → Prop}
    (hP : ∀ (s t : List α) (a b : α),
      ¬ R a b → ¬ R b a → P (s ++ a :: b :: t) → P (s ++ b :: a :: t))
    {l l' : List α} (h : UnrelatedSwapReachable R l l') (hl : P l) : P l' := by
  induction h with
  | refl => exact hl
  | tail h hstep ih =>
    obtain ⟨s, t, a, b, rfl, rfl, hab, hba⟩ := hstep
    exact hP s t a b hab hba ih

/-- Reachability keeps all list occurrences, including repetitions. -/
theorem UnrelatedSwapReachable.perm {l l' : List α}
    (h : UnrelatedSwapReachable R l l') : l.Perm l' := by
  apply h.preserves (P := fun m => l.Perm m) _ (List.Perm.refl l)
  intro s t a b _ _ hm
  exact hm.trans ((List.Perm.swap b a t).append_left s)

/-- Unrelated swaps leave the numerical inversion count unchanged. -/
theorem UnrelatedSwapReachable.inversions_eq [DecidableRel R] {l l' : List α}
    (h : UnrelatedSwapReachable R l l') :
    relationInversions R l' = relationInversions R l := by
  apply h.preserves (P := fun m => relationInversions R m = relationInversions R l) _ rfl
  intro s t a b hab hba hm
  exact (relationInversions_swap_unrelated R s t a b hab hba).trans hm

private theorem orderedInsert_preserves {β : Type v} [LinearOrder β]
    (x : α → β) (P : List α → Prop)
    (hP : ∀ (s t : List α) (a b : α), x a < x b →
      P (s ++ a :: b :: t) → P (s ++ b :: a :: t))
    (m : List α) : ∀ (s t : List α) (a : α),
      P (s ++ a :: m ++ t) →
        P (s ++ List.orderedInsert (fun a b => x b ≤ x a) a m ++ t) := by
  induction m with
  | nil => intro s t a hm; simpa using hm
  | cons b m ih =>
    intro s t a hm
    by_cases hab : x b ≤ x a
    · simpa only [List.orderedInsert_cons, ite_eq_left hab] using hm
    · have hswap := hP s (m ++ t) a b (lt_of_not_ge hab) (by simpa using hm)
      have hnew := ih (s ++ [b]) t a (by simpa [List.append_assoc] using hswap)
      simpa [List.orderedInsert_cons, hab, List.append_assoc] using hnew

private theorem insertionSort_preserves {β : Type v} [LinearOrder β]
    (x : α → β) (P : List α → Prop)
    (hP : ∀ (s t : List α) (a b : α), x a < x b →
      P (s ++ a :: b :: t) → P (s ++ b :: a :: t))
    (m : List α) : ∀ (s t : List α), P (s ++ m ++ t) →
      P (s ++ List.insertionSort (fun a b => x b ≤ x a) m ++ t) := by
  induction m with
  | nil => intro s t hm; simpa using hm
  | cons a m ih =>
    intro s t hm
    have htail := ih (s ++ [a]) t (by simpa [List.append_assoc] using hm)
    simpa only [List.insertionSort_cons] using
      orderedInsert_preserves x P hP (List.insertionSort (fun a b => x b ≤ x a) m)
        s t a (by simpa [List.append_assoc] using htail)

/-- If an invariant forbids every adjacent relation pair, unrelated-swap
closure forbids every forward relation pair. A strict ordering of `R` is supplied
as a key; the theorem does not assume transitivity of `R`. -/
theorem relationInversions_eq_zero_of_closed {β : Type v} [LinearOrder β]
    [DecidableRel R] (x : α → β) (hx : ∀ a b, R a b → x a < x b)
    (P : List α → Prop)
    (hP : ∀ (s t : List α) (a b : α), ¬ R a b → ¬ R b a →
      P (s ++ a :: b :: t) → P (s ++ b :: a :: t))
    (hno : ∀ (s t : List α) (a b : α), P (s ++ a :: b :: t) → ¬ R a b)
    {l : List α} (hl : P l) : relationInversions R l = 0 := by
  let Q m := P m ∧ relationInversions R m = relationInversions R l
  have hQ : ∀ (s t : List α) (a b : α), x a < x b →
      Q (s ++ a :: b :: t) → Q (s ++ b :: a :: t) := by
    intro s t a b hab hq
    have hnab := hno s t a b hq.1
    have hnba : ¬ R b a := fun h => (not_lt_of_ge hab.le) (hx b a h)
    exact ⟨hP s t a b hnab hnba hq.1,
      (relationInversions_swap_unrelated R s t a b hnab hnba).trans hq.2⟩
  have hs : Q (List.insertionSort (fun a b => x b ≤ x a) l) := by
    simpa using insertionSort_preserves x Q hQ l [] []
      (by simpa using (show Q l from ⟨hl, rfl⟩))
  have hsorted := List.pairwise_insertionSort (fun a b => x b ≤ x a) l
  have hz : relationInversions R (List.insertionSort (fun a b => x b ≤ x a) l) = 0 := by
    apply (relationInversions_eq_zero_iff R _).mpr
    exact hsorted.imp fun hle hr => (not_lt_of_ge hle) (hx _ _ hr)
  exact hs.2.symm.trans hz

/-- An inversion of an acyclic relation can be exposed as an adjacent pair by
swapping only pairs unrelated in both directions. -/
theorem exists_adjacent_relation_of_inversions_pos [DecidableRel R]
    (hacyc : ∀ a, ¬ Relation.TransGen R a a) {l : List α}
    (hl : 0 < relationInversions R l) :
    ∃ (s t : List α) (a b : α),
      UnrelatedSwapReachable R l (s ++ a :: b :: t) ∧ R a b := by
  classical
  let : IsStrictOrder α (Relation.TransGen R) :=
    { irrefl := hacyc, trans := fun _ _ _ h h' => h.trans h' }
  let : PartialOrder α := partialOrderOfSO (Relation.TransGen R)
  let x : α → LinearExtension α := toLinearExtension
  have hx : ∀ a b, R a b → x a < x b := by
    intro a b hab
    exact toLinearExtension.monotone.strictMono_of_injective (fun _ _ h => h)
      (Relation.TransGen.single hab)
  by_contra h
  have hno : ∀ (s t : List α) (a b : α),
      UnrelatedSwapReachable R l (s ++ a :: b :: t) → ¬ R a b := by
    intro s t a b hs hab
    exact h ⟨s, t, a, b, hs, hab⟩
  have hz := relationInversions_eq_zero_of_closed x hx (UnrelatedSwapReachable R l)
    (fun s t a b hab hba hs => hs.trans (.swap s t a b hab hba))
    hno (.refl l)
  omega

end Langlands.Combinatorics
