import Langlands.Group.RelativeWeylJacquetProof

/-! # Weighted longest-representative cancellation -/

noncomputable section

universe u v uA

namespace Langlands.Group.RelativeWeylIndexing

open Classical
open scoped BigOperators

variable {B : Type u} {W : Type v} [Group W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)
variable [Fintype B]

/-- Double-coset minimality separates into left minimality and right ascents. -/
theorem isMinimal_iff_right_subset_positiveSimpleSet
    (J I : Finset B) (w : W) :
    IsMinimal cs J I w ↔
      IsMinimal cs J ∅ w ∧ I ⊆ positiveSimpleSet cs w := by
  rw [minimalityLengthCriterion_proof cs J I w,
    minimalityLengthCriterion_proof cs J ∅ w]
  constructor
  · rintro ⟨hJ, hI⟩
    exact ⟨⟨hJ, by simp⟩, fun i hi =>
      (mem_positiveSimpleSet cs w i).mpr (hI i hi)⟩
  · rintro ⟨⟨hJ, -⟩, hI⟩
    exact ⟨hJ, fun i hi => (mem_positiveSimpleSet cs w i).mp (hI hi)⟩

variable {A : Type uA} [AddCommGroup A]
variable [Fintype W]

/-- The signed minimal-double-coset expansion with weights indexed by the
simple-image intersection. -/
def jacquetWeightedExpansion
    (J : Finset B) (F : W → Finset B → A) : A :=
  ∑ I : Finset B, (-1 : ℤ) ^ I.card •
    ∑ w ∈ minimalReps cs J I, F w (simpleImage cs w I ∩ J)

/-- Jacquet coefficient cancellation with arbitrary additive weights. -/
theorem jacquet_weighted_powerset_sum
    (J : Finset B) (w : W) (hw : IsMinimal cs J ∅ w)
    (F : Finset B → A) :
    (∑ I ∈ (positiveSimpleSet cs w).powerset,
      (-1 : ℤ) ^ I.card • F (simpleImage cs w I ∩ J)) =
      if w = longestRep cs J
      then ∑ K ∈ J.powerset, (-1 : ℤ) ^ K.card • F K
      else 0 := by
  have hgroup :
      (∑ I ∈ (positiveSimpleSet cs w).powerset,
        (-1 : ℤ) ^ I.card • F (simpleImage cs w I ∩ J)) =
      ∑ K ∈ J.powerset,
        (∑ I ∈ (positiveSimpleSet cs w).powerset,
          if simpleImage cs w I ∩ J = K then (-1 : ℤ) ^ I.card else 0) • F K := by
    calc
      _ = ∑ I ∈ (positiveSimpleSet cs w).powerset,
          ∑ K ∈ J.powerset,
            if simpleImage cs w I ∩ J = K
            then (-1 : ℤ) ^ I.card • F K else 0 := by
        apply Finset.sum_congr rfl
        intro I hI
        simp [Finset.mem_powerset.mpr (Finset.inter_subset_right
          (s₁ := simpleImage cs w I) (s₂ := J))]
      _ = ∑ K ∈ J.powerset,
          ∑ I ∈ (positiveSimpleSet cs w).powerset,
            if simpleImage cs w I ∩ J = K
            then (-1 : ℤ) ^ I.card • F K else 0 := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro K hK
        rw [Finset.sum_smul]
        apply Finset.sum_congr rfl
        intro I hI
        split_ifs <;> simp
  rw [hgroup]
  have hc := longestSurvivor_proof cs J w hw
  by_cases he : w = longestRep cs J
  · rw [ite_eq_left he]
    apply Finset.sum_congr rfl
    intro K hK
    rw [jacquetCancellation_proof cs J w hw K (Finset.mem_powerset.mp hK)]
    simp [hc.mpr he]
  · rw [ite_eq_right he]
    apply Finset.sum_eq_zero
    intro K hK
    rw [jacquetCancellation_proof cs J w hw K (Finset.mem_powerset.mp hK)]
    have hn : ¬ MapsIntoSimple cs w (positiveSimpleSet cs w) J :=
      fun h => he (hc.mp h)
    simp [hn]

/-- The finite signed Jacquet expansion retains only the specified longest
representative, for every family of additive weights. -/
theorem jacquet_weighted_sum
    (J : Finset B) (F : W → Finset B → A) :
    (∑ I : Finset B, (-1 : ℤ) ^ I.card •
      ∑ w ∈ minimalReps cs J I, F w (simpleImage cs w I ∩ J)) =
      ∑ K ∈ J.powerset, (-1 : ℤ) ^ K.card • F (longestRep cs J) K := by
  have hexpand (I : Finset B) :
      (-1 : ℤ) ^ I.card •
          (∑ w ∈ minimalReps cs J I, F w (simpleImage cs w I ∩ J)) =
        ∑ w : W, if IsMinimal cs J I w
          then (-1 : ℤ) ^ I.card • F w (simpleImage cs w I ∩ J) else 0 := by
    rw [Finset.smul_sum, minimalReps, Finset.sum_filter]
  have hinner (w : W) :
      (∑ I : Finset B, if IsMinimal cs J I w
        then (-1 : ℤ) ^ I.card • F w (simpleImage cs w I ∩ J) else 0) =
      if w = longestRep cs J
      then ∑ K ∈ J.powerset, (-1 : ℤ) ^ K.card • F w K else 0 := by
    by_cases hw : IsMinimal cs J ∅ w
    · have hrestrict :
          (∑ I : Finset B, if IsMinimal cs J I w
            then (-1 : ℤ) ^ I.card • F w (simpleImage cs w I ∩ J) else 0) =
          ∑ I ∈ (positiveSimpleSet cs w).powerset,
            (-1 : ℤ) ^ I.card • F w (simpleImage cs w I ∩ J) := by
        calc
          _ = ∑ I ∈ (positiveSimpleSet cs w).powerset,
              if IsMinimal cs J I w
              then (-1 : ℤ) ^ I.card • F w (simpleImage cs w I ∩ J) else 0 := by
            symm
            apply Finset.sum_subset (Finset.subset_univ _)
            intro I hI hnot
            have hn : ¬ IsMinimal cs J I w := by
              intro h
              exact hnot (Finset.mem_powerset.mpr
                ((isMinimal_iff_right_subset_positiveSimpleSet cs J I w).mp h).2)
            simp [hn]
          _ = _ := by
            apply Finset.sum_congr rfl
            intro I hI
            simp [(isMinimal_iff_right_subset_positiveSimpleSet cs J I w).mpr
              ⟨hw, Finset.mem_powerset.mp hI⟩]
      rw [hrestrict]
      exact jacquet_weighted_powerset_sum cs J w hw (F w)
    · have hn (I : Finset B) : ¬ IsMinimal cs J I w := by
        intro h
        exact hw ((isMinimal_iff_right_subset_positiveSimpleSet cs J I w).mp h).1
      have he : w ≠ longestRep cs J := by
        rintro rfl
        exact hw ((mem_minimalReps cs J ∅ _).mp (longestRep_mem cs J))
      simp [hn, he]
  rw [Finset.sum_congr rfl (fun I _ => hexpand I), Finset.sum_comm,
    Finset.sum_congr rfl (fun w _ => hinner w)]
  simp

/-- The constructed signed expansion is the longest-representative sum. -/
theorem jacquetWeightedExpansion_eq_longest
    (J : Finset B) (F : W → Finset B → A) :
    jacquetWeightedExpansion cs J F =
      ∑ K ∈ J.powerset, (-1 : ℤ) ^ K.card • F (longestRep cs J) K :=
  jacquet_weighted_sum cs J F

end Langlands.Group.RelativeWeylIndexing
