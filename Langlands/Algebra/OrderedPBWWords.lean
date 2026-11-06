import Langlands.Algebra.OrderedPBWMonomials
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Shortlex
import Mathlib.Tactic

noncomputable section
universe u v
set_option autoImplicit false

namespace Langlands.Algebra.UniversalEnveloping

/-- The ascending word associated with an exponent vector. -/
def exponentWord {n : ℕ} (e : Fin n → ℕ) : List (Fin n) :=
  (List.ofFn fun i : Fin n => List.replicate (e i) i).flatten

theorem exponentWord_pairwise {n : ℕ} (e : Fin n → ℕ) :
    (exponentWord e).Pairwise (· ≤ ·) := by
  rw [exponentWord, List.pairwise_flatten]
  constructor
  · intro l hl
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
    exact List.pairwise_replicate.mpr (Or.inr le_rfl)
  · rw [List.pairwise_ofFn]
    intro i j hij x hx y hy
    have hx' : x = i := List.eq_of_mem_replicate hx
    have hy' : y = j := List.eq_of_mem_replicate hy
    simpa [hx', hy'] using le_of_lt hij

theorem exponentWord_count {n : ℕ} (e : Fin n → ℕ) (i : Fin n) :
    (exponentWord e).count i = e i := by
  simp [exponentWord, List.count_flatten, List.sum_ofFn, List.count_replicate]

theorem pairwise_eq_exponentWord {n : ℕ} (w : List (Fin n))
    (hw : w.Pairwise (· ≤ ·)) :
    w = exponentWord (fun i => w.count i) := by
  apply List.Perm.eq_of_pairwise' hw (exponentWord_pairwise _)
  apply List.perm_iff_count.mpr
  intro i
  simp [exponentWord_count]

theorem exponentWord_injective {n : ℕ} :
    Function.Injective (exponentWord (n := n)) := by
  intro e f h
  funext i
  simpa only [exponentWord_count] using congrArg (fun w => w.count i) h

/-- Exponent vectors and ascending finite words give equivalent basis index types. -/
def exponentWordEquiv {n : ℕ} :
    (Fin n → ℕ) ≃ {w : List (Fin n) // w.Pairwise (· ≤ ·)} where
  toFun e := ⟨exponentWord e, exponentWord_pairwise e⟩
  invFun w i := w.val.count i
  left_inv e := funext (exponentWord_count e)
  right_inv w := Subtype.ext (pairwise_eq_exponentWord w.val w.property).symm

theorem exponentWord_product {k : Type u} {L : Type v} [Field k]
    [LieRing L] [LieAlgebra k L] {n : ℕ} (b : Module.Basis (Fin n) k L)
    (e : Fin n → ℕ) :
    ((exponentWord e).map fun i => UniversalEnvelopingAlgebra.ι k (b i)).prod =
      orderedPBWMonomial b e := by
  simp [exponentWord, List.map_flatten, List.prod_flatten, List.map_ofFn,
    List.map_replicate, List.prod_replicate, orderedPBWMonomial, Function.comp_def]

/-- Any word that is not ascending contains an adjacent inversion. -/
theorem exists_adjacent_inversion {α : Type*} [LinearOrder α] (w : List α)
    (hw : ¬ w.Pairwise (· ≤ ·)) :
    ∃ (a : List α) (i j : α) (c : List α), w = a ++ i :: j :: c ∧ j < i := by
  induction w with
  | nil => exact (hw (by simp)).elim
  | cons i w ih =>
    by_cases ht : w.Pairwise (· ≤ ·)
    · cases w with
      | nil => exact (hw (by simp)).elim
      | cons j w =>
        refine ⟨[], i, j, w, rfl, ?_⟩
        by_contra h
        apply hw
        rw [List.pairwise_cons]
        refine ⟨?_, ht⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact le_of_not_gt h
        · exact (le_of_not_gt h).trans ((List.pairwise_cons.mp ht).1 x hx)
    · obtain ⟨a, j, l, c, rfl, hlj⟩ := ih ht
      exact ⟨i :: a, j, l, c, rfl, hlj⟩

/-- Swapping an adjacent inversion decreases shortlex order. -/
theorem shortlex_adjacent_swap {α : Type*} [LinearOrder α]
    (a : List α) (i j : α) (c : List α) (h : j < i) :
    List.Shortlex (· < ·) (a ++ j :: i :: c) (a ++ i :: j :: c) := by
  apply List.Shortlex.append_left
  apply List.Shortlex.of_lex (by simp)
  exact List.Lex.rel h

end Langlands.Algebra.UniversalEnveloping
