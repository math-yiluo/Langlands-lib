/-
Adapted from the Anthropic Lean formalisation of Fermat's Last Theorem, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, files
`Definitions/Def_DifferentFiltrationFormula.lean`.
Copyright 2026 Anthropic, PBC. Licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: statements are on the Library's `Langlands.Ramification.lowerGroup`; names follow the
Library; no options are set.
The paired Markdown file lists the changes.
-/

import Langlands.LocalFactor.Ramification.Filtration
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.DedekindDomain.Different

/-!
# The different and the sum over the lower filtration

For a group acting on a local ring `B`, the sum `∑_{i<N} (|G_i| - 1)` over the lower filtration
(`lowerGroupFiltrationSum`), its stability once `G_N` is trivial, and its expression as a sum over
`σ ≠ 1` of the number of `i < N` with `σ ∈ G_i` (`lowerGroupDepthCount`). The proposition
`DifferentEqPowFiltrationSum A B G` states Hilbert's formula for the different of `B` over `A`: the
different ideal is the maximal ideal of `B` to the power of the filtration sum. It is a statement
only; nothing here proves it.
-/

namespace Langlands.Ramification

section

open scoped Pointwise

attribute [local instance] FractionRing.liftAlgebra

section FiltrationSum

variable (B : Type*) [CommRing B] [IsLocalRing B]
variable (G : Type*) [Group G] [MulSemiringAction G B]

noncomputable def lowerGroupFiltrationSum (N : ℕ) : ℕ :=
  ∑ i ∈ Finset.range N, (Nat.card (lowerGroup B G i) - 1)

noncomputable def lowerGroupDepthCount (N : ℕ) (σ : G) : ℕ :=
  letI : DecidablePred fun i => σ ∈ lowerGroup B G i :=
    fun _ => Classical.propDecidable _
  ((Finset.range N).filter fun i => σ ∈ lowerGroup B G i).card

variable {B G}

theorem lowerGroup_eq_bot_of_le {N M : ℕ}
    (hN : lowerGroup B G N = ⊥) (hNM : N ≤ M) :
    lowerGroup B G M = ⊥ :=
  le_bot_iff.mp (hN ▸ (lowerGroup_antitone _ _) hNM)

theorem lowerGroupFiltrationSum_eq_of_le {N M : ℕ}
    (hN : lowerGroup B G N = ⊥) (hNM : N ≤ M) :
    lowerGroupFiltrationSum B G M = lowerGroupFiltrationSum B G N := by
  unfold lowerGroupFiltrationSum
  rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le N) hNM,
    ← Finset.range_eq_Ico]
  have h0 : ∀ i ∈ Finset.Ico N M,
      Nat.card (lowerGroup B G i) - 1 = 0 := by
    intro i hi
    rw [lowerGroup_eq_bot_of_le hN (Finset.mem_Ico.mp hi).1, Subgroup.card_bot]
  rw [Finset.sum_eq_zero h0, add_zero]

theorem lowerGroupFiltrationSum_eq_of_eq_bot {N M : ℕ}
    (hN : lowerGroup B G N = ⊥)
    (hM : lowerGroup B G M = ⊥) :
    lowerGroupFiltrationSum B G N = lowerGroupFiltrationSum B G M := by
  rcases le_total N M with h | h
  · exact (lowerGroupFiltrationSum_eq_of_le hN h).symm
  · exact lowerGroupFiltrationSum_eq_of_le hM h

private theorem sum_erase_one_ite_mem [Fintype G] [DecidableEq G] (H : Subgroup G)
    [DecidablePred (· ∈ H)] :
    (∑ σ ∈ Finset.univ.erase (1 : G), if σ ∈ H then 1 else 0) = Nat.card H - 1 := by
  classical
  rw [← Finset.card_filter, Finset.filter_erase,
    Finset.card_erase_of_mem (by simp [H.one_mem]), Nat.card_eq_fintype_card,
    Fintype.card_subtype]

theorem sum_lowerGroupDepthCount_erase_one [Fintype G] [DecidableEq G] (N : ℕ) :
    (∑ σ ∈ Finset.univ.erase (1 : G), lowerGroupDepthCount B G N σ)
      = lowerGroupFiltrationSum B G N := by
  classical
  simp only [lowerGroupDepthCount, lowerGroupFiltrationSum, Finset.card_filter]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ =>
    sum_erase_one_ite_mem (lowerGroup B G i)

end FiltrationSum

section StatementLayer

variable (A : Type*) [CommRing A] [IsDomain A]
variable (B : Type*) [CommRing B] [IsDedekindDomain B] [IsLocalRing B]
variable [Algebra A B] [Module.IsTorsionFree A B]
variable (G : Type*) [Group G] [MulSemiringAction G B]

def DifferentEqPowFiltrationSum : Prop :=
  ∀ N : ℕ, lowerGroup B G N = ⊥ →
    differentIdeal A B
      = IsLocalRing.maximalIdeal B ^ lowerGroupFiltrationSum B G N

variable {A B G}

theorem differentEqPowFiltrationSum_of_cutoff {N : ℕ}
    (hN : lowerGroup B G N = ⊥)
    (h : differentIdeal A B
      = IsLocalRing.maximalIdeal B ^ lowerGroupFiltrationSum B G N) :
    DifferentEqPowFiltrationSum A B G := by
  intro M hM
  rw [h, lowerGroupFiltrationSum_eq_of_eq_bot hN hM]

end StatementLayer

end

end Langlands.Ramification
