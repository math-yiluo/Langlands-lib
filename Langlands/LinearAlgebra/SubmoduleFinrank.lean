import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Finite sums of independent subspace dimensions -/

noncomputable section

open Module
open scoped BigOperators

namespace Langlands.Plancherel

/-- Dimensions add over finitely many independent subspaces. -/
theorem finrank_biSup_eq_sum {K V ι : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {p : ι → Submodule K V} (hp : iSupIndep p) (s : Finset ι) :
    Module.finrank K ↥(⨆ j ∈ s, p j) = ∑ j ∈ s, Module.finrank K (p j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, ← ih, Finset.iSup_insert]
    have hdisj : Disjoint (p a) (⨆ j ∈ s, p j) := by
      simpa using hp.disjoint_biSup (y := (s : Set ι)) (by simpa using ha)
    have h := Submodule.finrank_sup_add_finrank_inf_eq (p a) (⨆ j ∈ s, p j)
    rw [hdisj.eq_bot, finrank_bot, add_zero] at h
    exact h

end Langlands.Plancherel
