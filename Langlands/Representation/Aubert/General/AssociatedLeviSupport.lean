import Langlands.Representation.Aubert.General.CorrectedFiltration
import Langlands.Representation.Aubert.General.Terminal
import Langlands.Group.RelativeWeylAssociatedSubsetEquiv
import Langlands.Group.RelativeWeylLongestSurvivorProof

/-! The modified supports around the grade of the inverse longest representative. -/

noncomputable section

namespace Langlands.Aubert.General.CorrectedFiltration

open Langlands.Group.RelativeWeylIndexing

universe uI uW

variable {ι : Type uI} {W : Type uW} [Group W] [Fintype W]
variable {Mx : CoxeterMatrix ι} (cs : CoxeterSystem Mx W)

/-- A minimal double-coset representative for `(J, I)` at least as long as the
inverse longest representative of `D(I, ∅)` is that element. -/
theorem eq_inv_longestRep_of_isMinimal {J I : Finset ι} {x : W}
    (hx : IsMinimal cs J I x) (hlen : cs.length (longestRep cs I)⁻¹ ≤ cs.length x) :
    x = (longestRep cs I)⁻¹ := by
  have hx' : IsMinimal cs I ∅ x⁻¹ := isMinimal_inv cs fun a ha b hb =>
    hx a (standardSubgroup_mono cs (Finset.empty_subset J) ha) b hb
  have hmem : x⁻¹ ∈ minimalReps cs I ∅ := (mem_minimalReps cs I ∅ _).mpr hx'
  have heq : x⁻¹ = longestRep cs I := by
    refine longestRepresentativeUnique_proof cs I x⁻¹ hmem fun y hy => ?_
    rw [cs.length_inv]
    rw [cs.length_inv] at hlen
    exact (length_le_longestRep cs I hy).trans hlen
  rw [← heq, inv_inv]

variable [Fintype ι]

/-- The inverse longest representative is minimal in its double coset for
`(J, I)` only when `J` lies in the associated subset `I'`. -/
theorem subset_associatedSubset_of_isMinimal {J I : Finset ι}
    (hx : IsMinimal cs J I (longestRep cs I)⁻¹) : J ⊆ associatedSubset cs I := by
  intro j hj
  have hlt : cs.length (longestRep cs I)⁻¹ <
      cs.length (cs.simple j * (longestRep cs I)⁻¹) :=
    ((minimalityLengthCriterion_proof cs J I _).mp hx).1 j hj
  have hpos : j ∈ positiveSimpleSet cs (longestRep cs I) := by
    rw [mem_positiveSimpleSet, ← cs.length_inv (longestRep cs I),
      ← cs.length_inv (longestRep cs I * cs.simple j), mul_inv_rev, cs.inv_simple]
    exact hlt
  obtain ⟨k, hk, hkj⟩ := mapsIntoSimple_longestRep cs I j hpos
  classical
  unfold associatedSubset simpleImage
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ j, k, hk, ?_⟩
  rw [← hkj]
  group

/-- The inverse longest representative is minimal in its double coset for
`(I', I)`. -/
theorem isMinimal_associatedSubset (I : Finset ι) :
    IsMinimal cs (associatedSubset cs I) I (longestRep cs I)⁻¹ := by
  have hI : IsMinimal cs I ∅ (longestRep cs I) :=
    (mem_minimalReps cs I ∅ _).mp (longestRep_mem cs I)
  have hI' : IsMinimal cs (associatedSubset cs I) ∅ (longestRep cs I)⁻¹ := by
    rw [← longestRep_associatedSubset cs I]
    exact (mem_minimalReps cs _ ∅ _).mp (longestRep_mem cs _)
  refine (minimalityLengthCriterion_proof cs _ I _).mpr
    ⟨((minimalityLengthCriterion_proof cs _ ∅ _).mp hI').1, fun j hj => ?_⟩
  have h := ((minimalityLengthCriterion_proof cs I ∅ _).mp hI).1 j hj
  rw [← cs.length_inv (longestRep cs I)⁻¹, ← cs.length_inv ((longestRep cs I)⁻¹ * cs.simple j),
    mul_inv_rev, cs.inv_simple, inv_inv]
  exact h

theorem card_associatedSubset (I : Finset ι) :
    (associatedSubset cs I).card = I.card :=
  (associatedSubsetLaws_proof cs I).2.1

variable [DecidableEq W]

omit [Fintype ι] in
/-- The position of the inverse longest representative `(longestRep I)⁻¹` in the
decreasing-length enumeration of the Weyl group. -/
def associatedGrade (I : Finset ι) : ℕ :=
  ((Support.rankOrderedEquiv cs.length).symm (longestRep cs I)⁻¹).val

omit [Fintype ι] in
theorem associatedGrade_lt (I : Finset ι) :
    associatedGrade cs I < (Support.rankOrderedList cs.length).length :=
  ((Support.rankOrderedEquiv cs.length).symm (longestRep cs I)⁻¹).isLt

omit [Fintype ι] in
theorem rankOrderedElement_associatedGrade (I : Finset ι) :
    Support.rankOrderedElement cs.length (associatedGrade cs I) (associatedGrade_lt cs I) =
      (longestRep cs I)⁻¹ := by
  change Support.rankOrderedEquiv cs.length
    ((Support.rankOrderedEquiv cs.length).symm (longestRep cs I)⁻¹) = _
  exact Equiv.apply_symm_apply _ _

omit [Fintype ι] in
/-- A nonempty modified support contains a minimal double-coset representative. -/
theorem exists_isMinimal_of_mem_modifiedSupport {J I : Finset ι} {i : ℕ} {y : W}
    (hy : y ∈ modifiedSupport cs J I i) :
    ∃ x, IsMinimal cs J I x ∧ x ∈ Support.rankOrderedSupport cs.length i := by
  obtain ⟨x, ⟨a, ha, b, hb, rfl⟩, hx⟩ := exists_minimal_in_doubleCoset cs J I y
  exact ⟨_, hx, Support.modifiedRankSupport_subset _ _ _ i
    (Support.modifiedRankSupport_invariant _ _ _ i y hy a ha b hb)⟩

omit [Fintype ι] in
/-- Below the grade of `(longestRep I)⁻¹`, every modified support for the source
`I` is empty. -/
theorem modifiedSupport_associatedGrade_eq_empty (J I : Finset ι) :
    modifiedSupport cs J I (associatedGrade cs I) = ∅ := by
  ext y
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hy
  obtain ⟨x, hx, hxs⟩ := exists_isMinimal_of_mem_modifiedSupport cs hy
  have hlen : cs.length (longestRep cs I)⁻¹ ≤ cs.length x := by
    rw [← rankOrderedElement_associatedGrade cs I]
    exact Support.rankOrderedElement_rank_le _ _ _ x
      (Support.rankOrderedSupport_monotone _ (Nat.le_succ _) hxs)
  have hxw := eq_inv_longestRep_of_isMinimal cs hx hlen
  rw [hxw, ← rankOrderedElement_associatedGrade cs I] at hxs
  exact Support.rankOrderedElement_not_mem _ _ _ hxs

/-- At the grade after `(longestRep I)⁻¹`, the modified support for a target `J`
not contained in `I'` is still empty. -/
theorem modifiedSupport_associatedGrade_succ_eq_empty {J I : Finset ι}
    (hJ : ¬J ⊆ associatedSubset cs I) :
    modifiedSupport cs J I (associatedGrade cs I + 1) = ∅ := by
  ext y
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hy
  obtain ⟨x, hx, hxs⟩ := exists_isMinimal_of_mem_modifiedSupport cs hy
  have hlen : cs.length (longestRep cs I)⁻¹ ≤ cs.length x := by
    rw [← rankOrderedElement_associatedGrade cs I]
    exact Support.rankOrderedElement_rank_le _ _ _ x hxs
  have hxw := eq_inv_longestRep_of_isMinimal cs hx hlen
  rw [hxw] at hx
  exact hJ (subset_associatedSubset_of_isMinimal cs hx)

/-- In terminal degree zero the grade of `(longestRep I)⁻¹` is the last one. -/
theorem length_rankOrderedList_le_associatedGrade_succ (I : Finset ι)
    (hd : Complex.terminalDegree I = 0) :
    (Support.rankOrderedList cs.length).length ≤ associatedGrade cs I + 1 := by
  have hIu : I = Finset.univ := by
    apply Finset.eq_univ_of_card
    have hI := Finset.card_le_univ I
    unfold Complex.terminalDegree at hd
    omega
  have hone : (longestRep cs I)⁻¹ = 1 := by
    have h := isMinimal_associatedSubset cs I 1
      (standardSubgroup cs (associatedSubset cs I)).one_mem ((longestRep cs I)⁻¹)⁻¹ (by
        rw [hIu, standardSubgroup_univ]
        exact Subgroup.mem_top _)
    rw [one_mul, mul_inv_cancel, cs.length_one, Nat.le_zero, cs.length_eq_zero_iff] at h
    exact h
  by_contra hlt
  rw [not_le] at hlt
  have hanti := Support.rankOrderedEquiv_antitone cs.length
    (show (⟨associatedGrade cs I, associatedGrade_lt cs I⟩ :
        Fin (Support.rankOrderedList cs.length).length) ≤ ⟨associatedGrade cs I + 1, hlt⟩ from
      Nat.le_succ _)
  simp only at hanti
  have he : Support.rankOrderedEquiv cs.length
      ⟨associatedGrade cs I, associatedGrade_lt cs I⟩ = 1 := by
    rw [← hone]
    exact rankOrderedElement_associatedGrade cs I
  rw [he, cs.length_one, Nat.le_zero, cs.length_eq_zero_iff, ← he] at hanti
  have := congrArg Fin.val ((Support.rankOrderedEquiv cs.length).injective hanti)
  simp at this

variable [DecidableEq ι]

omit [DecidableEq W] in
/-- The coordinate `S \ I'` of the terminal degree of `I`: its target index is
the associated subset `I'`. -/
def associatedCoordinate (I : Finset ι) :
    {s : Finset ι // s.card = Complex.terminalDegree I} :=
  ⟨Finset.univ \ associatedSubset cs I, by
    rw [Finset.card_univ_sdiff, card_associatedSubset]
    rfl⟩

omit [DecidableEq W] in
theorem univ_sdiff_associatedCoordinate (I : Finset ι) :
    Finset.univ \ (associatedCoordinate cs I).1 = associatedSubset cs I := by
  ext j
  simp [associatedCoordinate]

omit [DecidableEq W] in
/-- The target of the surviving coordinate is minimal for the inverse longest
representative. -/
theorem isMinimal_associatedCoordinate (I : Finset ι) :
    IsMinimal cs (Finset.univ \ (associatedCoordinate cs I).1) I (longestRep cs I)⁻¹ := by
  rw [univ_sdiff_associatedCoordinate]
  exact isMinimal_associatedSubset cs I

omit [DecidableEq W] in
theorem associatedSubset_subset_associatedCoordinate (I : Finset ι) :
    associatedSubset cs I ⊆ Finset.univ \ (associatedCoordinate cs I).1 := by
  rw [univ_sdiff_associatedCoordinate]

/-- The lower step of the surviving coordinate vanishes. -/
theorem modifiedSupport_associatedCoordinate_eq_empty (I : Finset ι) :
    modifiedSupport cs (Finset.univ \ (associatedCoordinate cs I).1) I
      (associatedGrade cs I) = ∅ :=
  modifiedSupport_associatedGrade_eq_empty cs _ I

/-- Every coordinate of degree one less than the terminal degree has empty modified
support at the grade after `(longestRep I)⁻¹`. -/
theorem modifiedSupport_lower_eq_empty (I : Finset ι) (s : Finset ι)
    (hs : s.card + 1 = Complex.terminalDegree I) :
    modifiedSupport cs (Finset.univ \ s) I (associatedGrade cs I + 1) = ∅ := by
  apply modifiedSupport_associatedGrade_succ_eq_empty
  intro hsub
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_univ_sdiff, card_associatedSubset] at hcard
  have hI := Finset.card_le_univ I
  unfold Complex.terminalDegree at hs
  omega

/-- Every other coordinate of the terminal degree has empty modified support at the
grade after `(longestRep I)⁻¹`. -/
theorem modifiedSupport_other_eq_empty (I : Finset ι)
    (s : {s : Finset ι // s.card = Complex.terminalDegree I})
    (hs : s ≠ associatedCoordinate cs I) :
    modifiedSupport cs (Finset.univ \ s.1) I (associatedGrade cs I + 1) = ∅ := by
  apply modifiedSupport_associatedGrade_succ_eq_empty
  intro hsub
  apply hs
  have hcard : (associatedSubset cs I).card ≤ (Finset.univ \ s.1).card := by
    rw [Finset.card_univ_sdiff, card_associatedSubset, s.2]
    unfold Complex.terminalDegree
    have hI := Finset.card_le_univ I
    omega
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  apply Subtype.ext
  change s.1 = Finset.univ \ associatedSubset cs I
  rw [← heq]
  ext j
  simp

end Langlands.Aubert.General.CorrectedFiltration
