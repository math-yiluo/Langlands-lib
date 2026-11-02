import Langlands.Representation.Aubert.General.AlternatingOperator
import Langlands.Group.RelativeWeylIndexingTargets

/-!
# Target for longest-representative compatibility with Jacquet restriction
-/

noncomputable section

namespace Langlands.Aubert.General

universe uI uG uV

open Langlands.Group

/-- Convert equality of actual conjugate subgroup images to the membership
equivalence needed by the actual continuous conjugation transport. -/
theorem conjugationMembership_of_map_eq
    {G : Type uG} [Group G] (g : G) {L N : Subgroup G}
    (hLN : L.map (MulAut.conj g : G →* G) = N) :
    ∀ x : G, x ∈ N ↔ g⁻¹ * x * g ∈ L := by
  intro x
  rw [← hLN, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro hx
    exact ⟨g⁻¹ * x * g, hx, by simp [MulAut.conj_apply, mul_assoc]⟩

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {ι : Type uI} [Fintype ι]

/-- The Jacquet equation of Aubert Theorem 1.7(2), with `w_J` the specified
longest member of `D(J,∅)` in the actual relative Weyl quotient and
`J' = w_J⁻¹(J)`. Every normalizer lift acts by the actual conjugation
transport from `M J'` to `M J`. The named associated-Levi comparison is a
visible structural prerequisite, not the desired K0 equation. -/
def JacquetCompatibilityStatement
    (P M U : Finset ι → Subgroup G)
    (h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I))
    (hU : ∀ I, IsClosed (U I : Set G))
    (hfl : ∀ I, ParabolicFiniteLength.{uG, max uG uV} (h I) (hU I))
    (hM : ∀ J, IsClosed (M J : Set G))
    (hLevi : ∀ (J : Finset ι) (I : Finset J),
      IsSemidirectDecomposition ((P (leviIndex J I)).subgroupOf (M J))
        ((M (leviIndex J I)).subgroupOf (M J))
        ((U (leviIndex J I)).subgroupOf (M J)))
    (hLeviFl : ∀ J, letI := (hM J).locallyCompactSpace
      ∀ I : Finset J, ParabolicFiniteLength.{uG, max uG uV} (hLevi J I)
        ((hU (leviIndex J I)).preimage continuous_subtype_val))
    (T : Subgroup G) [Fintype (RelativeWeyl.Weyl T)]
    {CM : CoxeterMatrix ι} (actual : RelativeWeylIndexing.ActualCoxeterSystem T CM)
    (hAssociated : RelativeWeylIndexing.actualAssociatedLeviConjugation T M actual) : Prop :=
  ∀ (J : Finset ι) (n : RelativeWeyl.normalizer T)
    (hn : QuotientGroup.mk n = RelativeWeylIndexing.longestRep actual J),
    let J' := RelativeWeylIndexing.associatedSubset actual J
    (jacquetK0 (h J) (hU J) (hfl J).2.2.1 (hfl J).2.2.2).comp
        (alternatingOperator P M U h hU hfl) =
      (conjugationK0 (n : G)
        (conjugationMembership_of_map_eq (n : G) (hAssociated J n hn))).comp
        ((leviAlternatingOperator P M U J' (hM J') (hLevi J') hU (hLeviFl J')).comp
          (jacquetK0 (h J') (hU J') (hfl J').2.2.1 (hfl J').2.2.2))

end Langlands.Aubert.General
