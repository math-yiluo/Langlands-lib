import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Order.BigOperators.Group.Multiset

/-! # Integral saturation of closed root sets -/

noncomputable section

namespace RootPairing

variable {J M N : Type*} [AddCommGroup M] [Module ℚ M]
    [AddCommGroup N] [Module ℚ N] (P : RootPairing J ℚ M N)

/-- A subset of the roots closed under addition whenever the sum is a root.
The definition allows nonreduced root pairings. -/
def IsAdditivelyClosedRootSet (X : Set M) : Prop :=
  X ⊆ Set.range P.root ∧
    ∀ α ∈ X, ∀ β ∈ X, α + β ∈ Set.range P.root → α + β ∈ X

variable [Finite J] [P.IsCrystallographic]

/-- A root which is a finite sum of members of a closed root set belongs to it. -/
theorem IsAdditivelyClosedRootSet.multiset_sum_mem {X : Set M}
    (hX : P.IsAdditivelyClosedRootSet X) (s : Multiset M)
    (hs : ∀ α ∈ s, α ∈ X) (hroot : s.sum ∈ Set.range P.root) :
    s.sum ∈ X := by
  classical
  induction s using Multiset.strongInductionOn with
  | ih s ih =>
    obtain ⟨i, hi⟩ := hroot
    have hsum : (s.map (P.coroot' i)).sum = 2 := by
      rw [← map_multiset_sum, ← hi, root_coroot'_eq_pairing, pairing_same]
    have hpos : ∃ α ∈ s, 0 < P.coroot' i α := by
      by_contra! h
      have hle := Multiset.sum_map_le_sum_map (P.coroot' i)
        (fun _ : M => (0 : ℚ)) h
      have : (s.map (P.coroot' i)).sum ≤ 0 := by simpa using hle
      linarith
    obtain ⟨α, hα, hαpos⟩ := hpos
    obtain ⟨j, hj⟩ := hX.1 (hs α hα)
    by_cases hij : j = i
    · rw [← hi, ← hij, hj]
      exact hs α hα
    have hpair : 0 < P.pairingIn ℤ j i := by
      have hp : 0 < P.pairing j i := by
        simpa only [← hj, root_coroot'_eq_pairing] using hαpos
      rw [← P.algebraMap_pairingIn ℤ] at hp
      simpa [algebraMap_int_eq] using hp
    have hdiff : s.sum - α ∈ Set.range P.root := by
      rw [← hi, ← hj, ← neg_sub, neg_mem_range_root_iff]
      exact P.root_sub_root_mem_of_pairingIn_pos hpair hij
    have heq : (s.erase α).sum = s.sum - α := by
      have ht := congrArg Multiset.sum (Multiset.cons_erase hα)
      apply eq_sub_of_add_eq'
      simpa only [Multiset.sum_cons] using ht
    have htail : (s.erase α).sum ∈ X :=
      ih (s.erase α) (Multiset.erase_lt.mpr hα)
        (fun β hβ => hs β (Multiset.mem_of_mem_erase hβ)) (heq.symm ▸ hdiff)
    have ht := hX.2 α (hs α hα) (s.sum - α) (heq ▸ htail)
      (by simpa only [add_sub_cancel] using (show s.sum ∈ Set.range P.root from ⟨i, hi⟩))
    simpa only [add_sub_cancel] using ht

/-- Closed crystallographic root sets are saturated for integral positive sums.
This is weaker than saturation for rational or real nonnegative combinations. -/
theorem IsAdditivelyClosedRootSet.mem_closure_iff {X : Set M}
    (hX : P.IsAdditivelyClosedRootSet X) {α : M}
    (hα : α ∈ Set.range P.root) :
    α ∈ AddSubmonoid.closure X ↔ α ∈ X := by
  constructor
  · intro h
    obtain ⟨s, hs, rfl⟩ := AddSubmonoid.exists_multiset_of_mem_closure h
    exact hX.multiset_sum_mem P s hs hα
  · intro h
    exact AddSubmonoid.subset_closure h

end RootPairing
