import Langlands.Representation.Aubert.General.AlternatingOperator

/-! # Target for compatibility with induction from every standard Levi -/

noncomputable section

namespace Langlands.Aubert.General

universe uI uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {ι : Type uI} [Fintype ι]

/-- The induction equation of Aubert Theorem 1.7(2), for every standard
subset `J`, with the actual Levi operator and no additional rank sign.
The connected reductive realization and the proof remain separate. -/
def InductionCompatibilityStatement
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
        ((hU (leviIndex J I)).preimage continuous_subtype_val)) : Prop :=
  ∀ J : Finset ι,
    (alternatingOperator P M U h hU hfl).comp
        (inductionK0 (h J) (hU J) (hfl J).1 (hfl J).2.1) =
      (inductionK0 (h J) (hU J) (hfl J).1 (hfl J).2.1).comp
        (leviAlternatingOperator P M U J (hM J) (hLevi J) hU (hLeviFl J))

end Langlands.Aubert.General
