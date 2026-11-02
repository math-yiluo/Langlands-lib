import Langlands.Group.RelativeWeylJacquetProof
import Langlands.Group.RelativeWeylStandardIntersectionProof
import Langlands.Group.RelativeWeylLongestSurvivorProof
import Langlands.Group.RelativeWeylIndexingTargets
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Solomon's alternating intersection coefficient

Exchanging the two sums reduces the coefficient to one inner sum for each
right-`J`-minimal `w`. At such `w` the inner sum is the Jacquet cancellation
sum at `w⁻¹`, and the longest-survivor criterion leaves only
`w = (longestRep J)⁻¹`.
-/

namespace Langlands.Group.RelativeWeylIndexing

universe u v
variable {B : Type u} {W : Type v} [Group W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

open Classical
open scoped BigOperators
noncomputable section

/-- A simple reflection in `W_I` is indexed by `I`. -/
theorem mem_of_simple_mem_standardSubgroup [Fintype B] {I : Finset B} {k : B}
    (hk : cs.simple k ∈ standardSubgroup cs I) : k ∈ I := by
  by_contra hkI
  have hmin : ∀ i ∈ I,
      cs.length (cs.simple k) < cs.length (cs.simple i * cs.simple k) := by
    intro i hi
    have hik : i ≠ k := fun h => hkI (h ▸ hi)
    have hne : cs.simple i * cs.simple k ≠ 1 := by
      intro h
      apply hik
      apply simple_reflection_injective cs
      calc
        cs.simple i = (cs.simple k)⁻¹ := eq_inv_of_mul_eq_one_left h
        _ = cs.simple k := cs.inv_simple k
    have h0 : cs.length (cs.simple i * cs.simple k) ≠ 0 :=
      fun h => hne (cs.length_eq_zero_iff.mp h)
    rw [cs.length_simple]
    rcases cs.length_simple_mul (cs.simple k) i with h | h
    · rw [h, cs.length_simple]
      omega
    · rw [cs.length_simple] at h
      omega
  have h := left_minimal_of_simple cs hmin (cs.simple k) hk
  rw [cs.simple_mul_simple_self, cs.length_one, cs.length_simple] at h
  omega

/-- A length-one element of `W_I` is a simple reflection indexed by `I`. -/
theorem exists_simple_of_mem_standardSubgroup [Fintype B] {I : Finset B} {a : W}
    (ha : a ∈ standardSubgroup cs I) (h1 : cs.length a = 1) :
    ∃ i ∈ I, a = cs.simple i := by
  obtain ⟨i, rfl⟩ := cs.length_eq_one_iff.mp h1
  exact ⟨i, mem_of_simple_mem_standardSubgroup cs ha, rfl⟩

/-- Distinct simple subsets generate distinct standard subgroups. -/
theorem standardSubgroup_injective [Fintype B] {Q K : Finset B}
    (h : standardSubgroup cs Q = standardSubgroup cs K) : Q = K := by
  ext k
  constructor
  · intro hk
    have hs := simple_mem_standardSubgroup cs hk
    rw [h] at hs
    exact mem_of_simple_mem_standardSubgroup cs hs
  · intro hk
    have hs := simple_mem_standardSubgroup cs hk
    rw [← h] at hs
    exact mem_of_simple_mem_standardSubgroup cs hs

/-- At a minimal representative, a conjugate `w s_j w⁻¹` in `W_I`, with
`j ∈ J`, is a simple reflection indexed by `I`. -/
theorem exists_conj_simple_eq_of_isMinimal [Fintype B] {I J : Finset B} {w : W}
    (hw : IsMinimal cs I J w) {j : B} (hj : j ∈ J)
    (hmem : w * cs.simple j * w⁻¹ ∈ standardSubgroup cs I) :
    ∃ i ∈ I, w * cs.simple j * w⁻¹ = cs.simple i := by
  have hL : ∀ x ∈ standardSubgroup cs I, cs.length w ≤ cs.length (x * w) := by
    intro x hx
    simpa using hw x hx 1 (standardSubgroup cs J).one_mem
  have hadd := length_mul_of_left_minimal cs hL hmem
  rw [inv_mul_cancel_right] at hadd
  have hR := ((minimalityLengthCriterion_proof cs I J w).mp hw).2 j hj
  apply exists_simple_of_mem_standardSubgroup cs hmem
  rcases cs.length_mul_simple w j with h | h
  · omega
  · omega

/-- At a minimal representative, the intersection subset is cut out by
simple conjugates. -/
theorem intersectionSubset_eq_simpleImage_inter [Fintype B] {I J : Finset B} {w : W}
    (hw : IsMinimal cs I J w) :
    intersectionSubset cs I J w = simpleImage cs w⁻¹ I ∩ J := by
  ext j
  simp only [intersectionSubset, simpleImage, Finset.mem_filter, Finset.mem_inter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hj, hmem⟩
    obtain ⟨i, hi, he⟩ := exists_conj_simple_eq_of_isMinimal cs hw hj hmem
    refine ⟨⟨i, hi, ?_⟩, hj⟩
    rw [inv_inv, ← he]
    group
  · rintro ⟨⟨i, hi, he⟩, hj⟩
    refine ⟨hj, ?_⟩
    have hc : w * cs.simple j * w⁻¹ = cs.simple i := by
      rw [← he]
      group
    rw [hc]
    exact simple_mem_standardSubgroup cs hi

/-- Minimality in `W_I w W_J` splits into right `J`-minimality and the
containment of `I` in the left ascents of `w`. -/
theorem isMinimal_iff_subset_positiveSimpleSet [Fintype B] {I J : Finset B} {w : W} :
    IsMinimal cs I J w ↔ IsMinimal cs ∅ J w ∧ I ⊆ positiveSimpleSet cs w⁻¹ := by
  have hinv : ∀ i : B, cs.length (w⁻¹ * cs.simple i) = cs.length (cs.simple i * w) := by
    intro i
    rw [← cs.length_inv (w⁻¹ * cs.simple i), mul_inv_rev, inv_inv, cs.inv_simple]
  rw [minimalityLengthCriterion_proof cs I J w, minimalityLengthCriterion_proof cs ∅ J w]
  constructor
  · rintro ⟨hI, hJ⟩
    refine ⟨⟨fun i hi => absurd hi (Finset.notMem_empty i), hJ⟩, fun i hi => ?_⟩
    rw [mem_positiveSimpleSet, hinv, cs.length_inv]
    exact hI i hi
  · rintro ⟨⟨-, hJ⟩, hsub⟩
    refine ⟨fun i hi => ?_, hJ⟩
    have h := (mem_positiveSimpleSet cs w⁻¹ i).mp (hsub hi)
    rwa [hinv, cs.length_inv] at h

/-- For right-`J`-minimal `w`, the inner sum over `I` is the Jacquet
cancellation sum at `w⁻¹`. -/
theorem inner_sum_eq_jacquet_sum [Fintype B] {J K : Finset B} {w : W}
    (hw : IsMinimal cs ∅ J w) :
    (∑ I : Finset B, if IsMinimal cs I J w ∧
        rightIntersection cs I J w = standardSubgroup cs K then (-1 : ℤ) ^ I.card else 0) =
      ∑ I ∈ (positiveSimpleSet cs w⁻¹).powerset,
        if simpleImage cs w⁻¹ I ∩ J = K then (-1 : ℤ) ^ I.card else 0 := by
  have hsub := Finset.sum_subset (Finset.subset_univ (positiveSimpleSet cs w⁻¹).powerset)
    (f := fun I : Finset B => if IsMinimal cs I J w ∧
        rightIntersection cs I J w = standardSubgroup cs K then (-1 : ℤ) ^ I.card else 0)
    (by
      intro I _ hI
      rw [Finset.mem_powerset] at hI
      have hn : ¬IsMinimal cs I J w :=
        fun h => hI ((isMinimal_iff_subset_positiveSimpleSet cs).mp h).2
      simp [hn])
  rw [← hsub]
  apply Finset.sum_congr rfl
  intro I hI
  rw [Finset.mem_powerset] at hI
  have hmin : IsMinimal cs I J w :=
    (isMinimal_iff_subset_positiveSimpleSet cs).mpr ⟨hw, hI⟩
  rw [standardIntersection_proof cs I J w hmin, intersectionSubset_eq_simpleImage_inter cs hmin]
  by_cases hAK : simpleImage cs w⁻¹ I ∩ J = K
  · simp [hmin, hAK]
  · have hne : standardSubgroup cs (simpleImage cs w⁻¹ I ∩ J) ≠ standardSubgroup cs K :=
      fun h => hAK (standardSubgroup_injective cs h)
    simp [hAK, hne]

/-- Solomon's alternating coefficient, given Jacquet cancellation. -/
theorem solomonCancellation_of_jacquetCancellation [Fintype B] [Fintype W]
    (hJac : jacquetCancellation cs) : solomonCancellation cs := by
  intro J K hKJ
  have hexp : ∀ I : Finset B, (-1 : ℤ) ^ I.card * (intersectionMultiplicity cs J I K : ℤ) =
      ∑ w : W, if IsMinimal cs I J w ∧ rightIntersection cs I J w = standardSubgroup cs K
        then (-1 : ℤ) ^ I.card else 0 := by
    intro I
    rw [intersectionMultiplicity, minimalReps, Finset.filter_filter,
      Finset.natCast_card_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    split_ifs <;> simp
  have hw : ∀ w : W, (∑ I : Finset B, if IsMinimal cs I J w ∧
        rightIntersection cs I J w = standardSubgroup cs K then (-1 : ℤ) ^ I.card else 0) =
      if w = (longestRep cs J)⁻¹ then (-1 : ℤ) ^ K.card else 0 := by
    intro w
    by_cases hR : IsMinimal cs ∅ J w
    · rw [inner_sum_eq_jacquet_sum cs hR, hJac J w⁻¹ (isMinimal_inv cs hR) K hKJ]
      have hiff : MapsIntoSimple cs w⁻¹ (positiveSimpleSet cs w⁻¹) J ↔
          w = (longestRep cs J)⁻¹ := by
        rw [longestSurvivor_proof cs J w⁻¹ (isMinimal_inv cs hR), inv_eq_iff_eq_inv]
      exact if_congr hiff rfl rfl
    · have h0 : ∀ I : Finset B, ¬IsMinimal cs I J w :=
        fun I h => hR ((isMinimal_iff_subset_positiveSimpleSet cs).mp h).1
      have hne : w ≠ (longestRep cs J)⁻¹ := by
        rintro rfl
        exact hR (isMinimal_inv cs ((mem_minimalReps cs J ∅ _).mp (longestRep_mem cs J)))
      simp [h0, hne]
  rw [Finset.sum_congr rfl (fun I _ => hexp I), Finset.sum_comm,
    Finset.sum_congr rfl (fun w _ => hw w)]
  simp

/-- Solomon's alternating intersection coefficient for every finite Coxeter
system. -/
theorem solomonCancellation_proof [Fintype B] [Fintype W] : solomonCancellation cs :=
  solomonCancellation_of_jacquetCancellation cs (jacquetCancellation_proof cs)

end

end Langlands.Group.RelativeWeylIndexing
