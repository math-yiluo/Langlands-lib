import Langlands.Representation.Aubert.General.InductionTarget
import Langlands.Representation.Aubert.General.LeviCuspidalEigenvalue

/-! # Assembly of Corollary 1.10(a) from induction compatibility -/

noncomputable section

namespace Langlands.Aubert.General

universe uI uG uV

open SmoothRep

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
  {ι : Type uI} [Fintype ι] [DecidableEq ι]
  (P M U : Finset ι → Subgroup G)
  (h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I))
  (hU : ∀ I, IsClosed (U I : Set G))
  (hfl : ∀ I, ParabolicFiniteLength.{uG, max uG uV} (h I) (hU I))
  (hM : ∀ J, IsClosed (M J : Set G))
  (hLevi : ∀ (J : Finset ι) (I : Finset J), IsSemidirectDecomposition
    ((P (leviIndex J I)).subgroupOf (M J))
    ((M (leviIndex J I)).subgroupOf (M J))
    ((U (leviIndex J I)).subgroupOf (M J)))

omit [DecidableEq ι] in
/-- Induction compatibility transports the actual inside-Levi cuspidal
eigenvalue to the induced class. The source's irreducibility hypotheses remain
in the conclusion. -/
theorem corollary110a_of_inductionCompatibility
    (hLeviFl : ∀ J, letI := (hM J).locallyCompactSpace
      ∀ I : Finset J, ParabolicFiniteLength.{uG, max uG uV} (hLevi J I)
        ((hU (leviIndex J I)).preimage continuous_subtype_val))
    (hcompat : InductionCompatibilityStatement P M U h hU hfl hM hLevi hLeviFl) :
    corollary110a P M U h hU hfl hM hLevi := by
  intro J σ _ hcusp _
  have he := LinearMap.congr_fun (hcompat J)
    (FiniteLengthGrothendieckGroup.ofObject σ)
  change alternatingOperator P M U h hU hfl
      (inductionK0 (h J) (hU J) (hfl J).1 (hfl J).2.1
        (FiniteLengthGrothendieckGroup.ofObject σ)) =
    inductionK0 (h J) (hU J) (hfl J).1 (hfl J).2.1
      (leviAlternatingOperator P M U J (hM J) (hLevi J) hU (hLeviFl J)
        (FiniteLengthGrothendieckGroup.ofObject σ)) at he
  rw [he, leviAlternatingOperator_ofObject_of_isCorollaryLeviCuspidal
    P M U J (h J) (hM J) (hLevi J) hU (hLeviFl J) σ hcusp, map_smul]

end Langlands.Aubert.General
