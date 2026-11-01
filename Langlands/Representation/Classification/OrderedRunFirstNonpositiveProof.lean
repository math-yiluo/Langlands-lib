import Langlands.Representation.Classification.OrderedRunFirstNonpositiveStatement
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith

/-! # The first nonpositive run: finite-sum proof -/

namespace Langlands.Classification

open scoped BigOperators

theorem orderedRunFirstNonpositive : OrderedRunFirstNonpositive := by
  classical
  intro k hk m a b hm ha htotal
  have hex : ∃ i : Fin k, a i + b i ≤ 0 := by
    by_contra h
    have hp : ∀ i : Fin k, 0 < a i + b i := by
      intro i
      exact lt_of_not_ge (fun hi => h ⟨i, hi⟩)
    have hsum : 0 < ∑ i : Fin k, (m i : ℝ) * (a i + b i) :=
      Finset.sum_pos (fun i _ => mul_pos (by exact_mod_cast hm i) (hp i))
        ⟨⟨0, hk⟩, Finset.mem_univ _⟩
    exact (not_lt_of_ge htotal) hsum
  let S : Finset (Fin k) := Finset.univ.filter (fun i => a i + b i ≤ 0)
  have hS : S.Nonempty := by
    obtain ⟨i, hi⟩ := hex
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  let i : Fin k := S.min' hS
  have hi : a i + b i ≤ 0 := (Finset.mem_filter.mp (Finset.min'_mem S hS)).2
  refine ⟨i, hi, ?_, ?_⟩
  · intro j hji
    have hj : 0 < a j + b j := by
      apply lt_of_not_ge
      intro hnon
      have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnon⟩
      exact (not_le_of_gt hji) (Finset.min'_le S j hjS)
    have haj : a j ≤ a i := ha hji.le
    exact ⟨hj, by linarith, haj⟩
  · intro hk2
    have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr hk2
    obtain ⟨j, hji⟩ := exists_ne i
    exact Finset.single_lt_sum hji (Finset.mem_univ i) (Finset.mem_univ j)
      (hm j) (fun _ _ _ => Nat.zero_le _)

end Langlands.Classification
