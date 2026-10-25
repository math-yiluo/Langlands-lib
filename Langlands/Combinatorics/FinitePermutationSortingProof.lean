import Langlands.Combinatorics.FinitePermutationSortingStatement
import Mathlib.Data.Finset.Max
import Mathlib.Order.Fin.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! # Finite sorting preserving an invariant

Minimize the position-weighted sum among the permutations satisfying the invariant.
-/

namespace Langlands.Combinatorics

private def sortingWeight {n : ℕ} (x : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) : ℝ :=
  ∑ i, (i.val : ℝ) * x (σ i)

private theorem sortingWeight_swap_sub {n : ℕ} (x : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) (a b : Fin n) (hab : a ≠ b) :
    sortingWeight x ((Equiv.swap a b).trans σ) - sortingWeight x σ =
      ((a.val : ℝ) - b.val) * (x (σ b) - x (σ a)) := by
  unfold sortingWeight
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_add_of_mem a b (Finset.mem_univ _) (Finset.mem_univ _) hab]
  · simp only [Equiv.trans_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
    ring
  · intro c _ hc
    simp only [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne hc.1 hc.2, sub_self]

private theorem sortingWeight_swap_lt {n : ℕ} (x : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) (a b : Fin n) (hab : a < b)
    (hx : x (σ a) < x (σ b)) :
    sortingWeight x ((Equiv.swap a b).trans σ) < sortingWeight x σ := by
  apply sub_neg.mp
  rw [sortingWeight_swap_sub x σ a b (ne_of_lt hab)]
  apply mul_neg_of_neg_of_pos
  · apply sub_neg.mpr
    exact_mod_cast hab
  · exact sub_pos.mpr hx

/-- Sorting preserves every invariant closed under adjacent strict inversions. -/
theorem finitePermutationSorting : FinitePermutationSorting := by
  classical
  intro n x P h0 hstep
  let S : Finset (Equiv.Perm (Fin n)) := Finset.univ.filter P
  have hS : S.Nonempty := ⟨Equiv.refl _, by simp [S, h0]⟩
  obtain ⟨σ, hσ, hmin⟩ := S.exists_min_image (sortingWeight x) hS
  have hP : P σ := (Finset.mem_filter.mp hσ).2
  refine ⟨σ, hP, ?_⟩
  cases n with
  | zero => intro i; exact Fin.elim0 i
  | succ n =>
    apply Fin.antitone_iff_succ_le.mpr
    intro i
    by_contra h
    have hi : x (σ i.castSucc) < x (σ i.succ) := lt_of_not_ge h
    have hnew := hstep σ hP i.val i.succ.isLt hi
    have hmem : (Equiv.swap i.castSucc i.succ).trans σ ∈ S := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnew⟩
    have hlt := sortingWeight_swap_lt x σ i.castSucc i.succ i.castSucc_lt_succ hi
    exact (not_lt_of_ge (hmin _ hmem)) hlt

end Langlands.Combinatorics
