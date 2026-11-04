import Langlands.Representation.Aubert.General.AssociatedLeviSupport
import Langlands.Representation.Aubert.General.CorrectedGradedContraction

/-! Left descents and conjugation at the inverse longest representative. -/

noncomputable section

namespace Langlands.Aubert.General.CorrectedFiltration

open Langlands.Group.RelativeWeylIndexing

universe uI uW

variable {ι : Type uI} {W : Type uW} [Group W] [Fintype W]
variable {Mx : CoxeterMatrix ι} (cs : CoxeterSystem Mx W) [Fintype ι]

/-- `W_{I'} = w W_I w⁻¹` for the inverse longest representative
`w = (longestRep I)⁻¹`. -/
theorem mem_standardSubgroup_associatedSubset_iff (I : Finset ι) (a : W) :
    a ∈ standardSubgroup cs (associatedSubset cs I) ↔
      ((longestRep cs I)⁻¹)⁻¹ * a * (longestRep cs I)⁻¹ ∈ standardSubgroup cs I := by
  rw [(associatedSubsetLaws_proof cs I).2.2, conjugateStandardSubgroup, Subgroup.mem_map]
  constructor
  · rintro ⟨b, hb, rfl⟩
    have h : ((longestRep cs I)⁻¹)⁻¹ * (MulAut.conj (longestRep cs I)⁻¹ : W →* W) b *
        (longestRep cs I)⁻¹ = b := by
      simp [mul_assoc]
    rw [h]
    exact hb
  · intro h
    refine ⟨_, h, ?_⟩
    simp [mul_assoc]

/-- `w = (longestRep I)⁻¹` is right-`I`-minimal. -/
theorem length_lt_inv_longestRep_mul_simple (I : Finset ι) :
    ∀ j ∈ I, cs.length (longestRep cs I)⁻¹ <
      cs.length ((longestRep cs I)⁻¹ * cs.simple j) :=
  right_length_lt_of_isMinimal cs (isMinimal_associatedSubset cs I)

/-- The left descents of `w = (longestRep I)⁻¹` are exactly `S \ I'`. -/
theorem leftDescentSet_inv_longestRep [DecidableEq ι] (I : Finset ι) :
    leftDescentSet cs (longestRep cs I)⁻¹ = Finset.univ \ associatedSubset cs I := by
  have hmin := isMinimal_associatedSubset cs I
  have hR := right_length_lt_of_isMinimal cs hmin
  ext j
  rw [mem_leftDescentSet, Finset.mem_sdiff]
  simp only [Finset.mem_univ, true_and]
  constructor
  · intro hj hjI
    exact hj (((minimalityLengthCriterion_proof cs _ I _).mp hmin).1 j hjI)
  · intro hjI hlt
    have hwL : ∀ i ∈ I, cs.length ((longestRep cs I)⁻¹)⁻¹ <
        cs.length (cs.simple i * ((longestRep cs I)⁻¹)⁻¹) := by
      intro i hi
      rw [← cs.length_inv (((longestRep cs I)⁻¹)⁻¹),
        ← cs.length_inv (cs.simple i * ((longestRep cs I)⁻¹)⁻¹), mul_inv_rev, inv_inv,
        cs.inv_simple]
      exact hR i hi
    have hxR : ∀ i ∈ I, cs.length (cs.simple j * (longestRep cs I)⁻¹) <
        cs.length (cs.simple j * (longestRep cs I)⁻¹ * cs.simple i) := by
      intro i hi
      by_contra hn
      have hd : cs.length (cs.simple j * (longestRep cs I)⁻¹ * cs.simple i) <
          cs.length (cs.simple j * (longestRep cs I)⁻¹) := by
        have := cs.length_mul_simple_ne (cs.simple j * (longestRep cs I)⁻¹) i
        omega
      have hd' : cs.length (cs.simple i * (((longestRep cs I)⁻¹)⁻¹ * cs.simple j)) <
          cs.length (((longestRep cs I)⁻¹)⁻¹ * cs.simple j) := by
        rw [← cs.length_inv (cs.simple i * (((longestRep cs I)⁻¹)⁻¹ * cs.simple j)),
          ← cs.length_inv (((longestRep cs I)⁻¹)⁻¹ * cs.simple j)]
        simpa [mul_inv_rev, mul_assoc, cs.inv_simple] using hd
      have hc := conj_simple_of_left_descent_mul_simple cs hwL hi hd'
      apply hjI
      classical
      unfold associatedSubset simpleImage
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ j, i, hi, ?_⟩
      rw [← hc]
      group
    have hxmin : IsMinimal cs ∅ I (cs.simple j * (longestRep cs I)⁻¹) :=
      (minimalityLengthCriterion_proof cs ∅ I _).mpr ⟨by simp, hxR⟩
    have heq := eq_inv_longestRep_of_isMinimal cs hxmin hlt.le
    rw [heq] at hlt
    exact lt_irrefl _ hlt

variable [DecidableEq W]

/-- The conjugation premise at the grade `associatedGrade cs I`. -/
theorem mem_standardSubgroup_associatedSubset_iff_rankOrderedElement (I : Finset ι) (a : W) :
    a ∈ standardSubgroup cs (associatedSubset cs I) ↔
      (Support.rankOrderedElement cs.length (associatedGrade cs I) (associatedGrade_lt cs I))⁻¹ *
          a * Support.rankOrderedElement cs.length (associatedGrade cs I)
            (associatedGrade_lt cs I) ∈ standardSubgroup cs I := by
  rw [rankOrderedElement_associatedGrade]
  exact mem_standardSubgroup_associatedSubset_iff cs I a

/-- Right-`I`-minimality at the grade `associatedGrade cs I`. -/
theorem length_lt_rankOrderedElement_associatedGrade_mul_simple (I : Finset ι) :
    ∀ j ∈ I, cs.length (Support.rankOrderedElement cs.length (associatedGrade cs I)
        (associatedGrade_lt cs I)) <
      cs.length (Support.rankOrderedElement cs.length (associatedGrade cs I)
        (associatedGrade_lt cs I) * cs.simple j) := by
  rw [rankOrderedElement_associatedGrade]
  exact length_lt_inv_longestRep_mul_simple cs I

/-- The left descents at the grade `associatedGrade cs I` are `S \ I'`. -/
theorem leftDescentSet_rankOrderedElement_associatedGrade [DecidableEq ι] (I : Finset ι) :
    leftDescentSet cs (Support.rankOrderedElement cs.length (associatedGrade cs I)
        (associatedGrade_lt cs I)) = Finset.univ \ associatedSubset cs I := by
  rw [rankOrderedElement_associatedGrade]
  exact leftDescentSet_inv_longestRep cs I

end Langlands.Aubert.General.CorrectedFiltration
