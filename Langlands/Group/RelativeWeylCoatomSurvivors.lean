import Langlands.Group.RelativeWeylAssociatedIndexing
import Langlands.Group.RelativeWeylAssociatedSubsetEquiv
import Langlands.Group.RelativeWeylSolomonProof

/-! # Simple-preserving pairs for a coatom source -/

namespace Langlands.Group.RelativeWeylIndexing

universe u v
variable {B : Type u} {W : Type v} [Group W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

open Classical
noncomputable section

/-- All equal-rank simple-preserving minimal pairs for the source `J`. -/
def simpleSurvivorPairs [Fintype B] [Fintype W] (J : Finset B) :
    Finset (Finset B × W) :=
  Finset.univ.filter (fun p =>
    p.1.card = J.card ∧ IsMinimal cs p.1 J p.2 ∧ MapsIntoSimple cs p.2 J p.1)

@[simp]
theorem mem_simpleSurvivorPairs [Fintype B] [Fintype W]
    (J I : Finset B) (w : W) :
    (I, w) ∈ simpleSurvivorPairs cs J ↔
      I.card = J.card ∧ IsMinimal cs I J w ∧ MapsIntoSimple cs w J I := by
  simp [simpleSurvivorPairs]

/-- At a minimal representative, fullness of the source intersection is
equivalent to the simple-preserving condition. -/
theorem intersectionSubset_eq_source_iff_mapsIntoSimple [Fintype B]
    {I J : Finset B} {w : W} (hw : IsMinimal cs I J w) :
    intersectionSubset cs I J w = J ↔ MapsIntoSimple cs w J I := by
  constructor
  · intro hfull j hj
    have hj' : j ∈ intersectionSubset cs I J w := hfull.symm ▸ hj
    exact exists_conj_simple_eq_of_isMinimal cs hw hj (Finset.mem_filter.mp hj').2
  · intro hm
    apply Finset.Subset.antisymm (intersectionSubset_subset cs I J w)
    intro j hj
    obtain ⟨i, hi, hji⟩ := hm j hj
    apply Finset.mem_filter.mpr
    refine ⟨hj, ?_⟩
    rw [hji]
    exact simple_mem_standardSubgroup cs hi

/-- All equal-rank minimal pairs with full source intersection. -/
def fullIntersectionPairs [Fintype B] [Fintype W] (J : Finset B) :
    Finset (Finset B × W) :=
  Finset.univ.filter (fun p =>
    p.1.card = J.card ∧ IsMinimal cs p.1 J p.2 ∧
      intersectionSubset cs p.1 J p.2 = J)

theorem fullIntersectionPairs_eq_simpleSurvivorPairs [Fintype B] [Fintype W]
    (J : Finset B) :
    fullIntersectionPairs cs J = simpleSurvivorPairs cs J := by
  ext ⟨I, w⟩
  simp only [fullIntersectionPairs, simpleSurvivorPairs, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hc, hm, hi⟩
    exact ⟨hc, hm, (intersectionSubset_eq_source_iff_mapsIntoSimple cs hm).mp hi⟩
  · rintro ⟨hc, hm, hs⟩
    exact ⟨hc, hm, (intersectionSubset_eq_source_iff_mapsIntoSimple cs hm).mpr hs⟩

/-- A coatom source leaves only the identity and inverse-longest pair. -/
theorem coatom_simpleSurvivor_classification [Fintype B] [Fintype W]
    (b : B) {I : Finset B} {w : W}
    (hcard : I.card = (Finset.univ.erase b).card)
    (hmin : IsMinimal cs I (Finset.univ.erase b) w)
    (hmaps : MapsIntoSimple cs w (Finset.univ.erase b) I) :
    (I = Finset.univ.erase b ∧ w = 1) ∨
      (I = associatedSubset cs (Finset.univ.erase b) ∧
        w = (longestRep cs (Finset.univ.erase b))⁻¹) := by
  let J := Finset.univ.erase b
  change I.card = J.card at hcard
  change IsMinimal cs I J w at hmin
  change MapsIntoSimple cs w J I at hmaps
  by_cases hw : w = 1
  · left
    refine ⟨?_, hw⟩
    have hsub : J ⊆ I := by
      intro j hj
      obtain ⟨i, hi, hji⟩ := hmaps j hj
      have he : j = i := simple_reflection_injective cs (by simpa [hw] using hji)
      exact he.symm ▸ hi
    exact (Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard)).symm
  · right
    obtain ⟨hleft, hright⟩ := (minimalityLengthCriterion_proof cs I J w).mp hmin
    obtain ⟨i, hi⟩ := cs.exists_rightDescent_of_ne_one hw
    have hdesc : cs.length (w * cs.simple i) < cs.length w := by
      have := cs.isRightDescent_iff.mp hi
      omega
    have hin : i ∉ J := by
      intro hij
      have := hright i hij
      omega
    have hib : i = b := by
      by_contra hn
      exact hin (by simp [J, hn])
    subst i
    have hpos : positiveSimpleSet cs w = J := by
      apply Finset.Subset.antisymm
      · intro j hj
        have hj' := (mem_positiveSimpleSet cs w j).mp hj
        have hjb : j ≠ b := by
          rintro rfl
          omega
        simp [J, hjb]
      · intro j hj
        exact (mem_positiveSimpleSet cs w j).mpr (hright j hj)
    have hmin0 : IsMinimal cs I ∅ w :=
      (minimalityLengthCriterion_proof cs I ∅ w).mpr ⟨hleft, by simp⟩
    have hlong : w = longestRep cs I :=
      (longestSurvivor_proof cs I w hmin0).mp (by simpa [hpos] using hmaps)
    have hJI : J = associatedSubset cs I := by
      rw [← positiveSimpleSet_longestRep, ← hlong, hpos]
    have hI : I = associatedSubset cs J := by
      rw [hJI, associatedSubset_involutive cs I]
    refine ⟨hI, ?_⟩
    rw [hlong, hI, longestRep_associatedSubset]

/-- Both canonical pairs satisfy the intrinsic minimality and simple-image
conditions, for every source subset. -/
theorem canonical_simpleSurvivorPairs [Fintype B] [Fintype W] (J : Finset B) :
    (J, 1) ∈ simpleSurvivorPairs cs J ∧
      (associatedSubset cs J, (longestRep cs J)⁻¹) ∈ simpleSurvivorPairs cs J := by
  constructor
  · apply (mem_simpleSurvivorPairs cs J J 1).mpr
    refine ⟨rfl, isMinimal_one cs J J, ?_⟩
    intro j hj
    exact ⟨j, hj, by simp⟩
  · apply (mem_simpleSurvivorPairs cs J _ _).mpr
    refine ⟨(associatedSubsetLaws_proof cs J).2.1, ?_, ?_⟩
    · rw [← longestRep_associatedSubset]
      apply (minimalityLengthCriterion_proof cs _ J _).mpr
      constructor
      · exact ((minimalityLengthCriterion_proof cs _ ∅ _).mp
          ((mem_minimalReps cs _ _ _).mp (longestRep_mem cs _))).1
      · intro j hj
        apply (mem_positiveSimpleSet cs _ j).mp
        rw [positiveSimpleSet_longestRep, associatedSubset_involutive]
        exact hj
    · rw [← longestRep_associatedSubset]
      have h := mapsIntoSimple_longestRep cs (associatedSubset cs J)
      rw [positiveSimpleSet_longestRep, associatedSubset_involutive] at h
      exact h

/-- The entire eligible set for a coatom source is the displayed pair set. -/
theorem simpleSurvivorPairs_coatom [Fintype B] [Fintype W] (b : B) :
    simpleSurvivorPairs cs (Finset.univ.erase b) =
      {(Finset.univ.erase b, 1),
        (associatedSubset cs (Finset.univ.erase b),
          (longestRep cs (Finset.univ.erase b))⁻¹)} := by
  ext ⟨I, w⟩
  constructor
  · intro hp
    obtain ⟨hc, hm, hs⟩ := (mem_simpleSurvivorPairs cs _ _ _).mp hp
    rcases coatom_simpleSurvivor_classification cs b hc hm hs with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  · intro hp
    rcases Finset.mem_insert.mp hp with he | he
    · cases he
      exact (canonical_simpleSurvivorPairs cs _).1
    · have he' := Finset.mem_singleton.mp he
      cases he'
      exact (canonical_simpleSurvivorPairs cs _).2

/-- The finite intrinsic budget used for a maximal-Levi source. -/
def CoatomSimpleSurvivorBoundStatement [Fintype B] [Fintype W] : Prop :=
  ∀ b : B, (simpleSurvivorPairs cs (Finset.univ.erase b)).card ≤ 2

theorem coatomSimpleSurvivorBound [Fintype B] [Fintype W] :
    CoatomSimpleSurvivorBoundStatement cs := by
  intro b
  rw [simpleSurvivorPairs_coatom]
  rcases Finset.card_pair_eq_one_or_two
      (a := (Finset.univ.erase b, (1 : W)))
      (b := (associatedSubset cs (Finset.univ.erase b),
        (longestRep cs (Finset.univ.erase b))⁻¹)) with h | h <;> omega

/-- The same budget counts full-intersection pairs, with their original
target-subset and representative indices. -/
theorem card_fullIntersectionPairs_coatom_le_two [Fintype B] [Fintype W] (b : B) :
    (fullIntersectionPairs cs (Finset.univ.erase b)).card ≤ 2 := by
  rw [fullIntersectionPairs_eq_simpleSurvivorPairs]
  exact coatomSimpleSurvivorBound cs b

end
end Langlands.Group.RelativeWeylIndexing
