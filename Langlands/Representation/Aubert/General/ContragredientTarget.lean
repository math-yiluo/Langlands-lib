import Langlands.Representation.Aubert.General.AlternatingOperator

/-!
# Target for commutation of the general Aubert operator with contragredients
-/

noncomputable section

namespace Langlands.Aubert.General

universe uI uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {ι : Type uI} [Fintype ι]

/-- Aubert Theorem 1.7(1): the unadjusted alternating operator commutes with
the actual smooth contragredient on the exact finite-length Grothendieck group.
This is a target on the supplied actual subgroup family; its connected
reductive realization and its proof are separate obligations. -/
def ContragredientCommutationStatement
    (P M U : Finset ι → Subgroup G)
    (h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I))
    (hU : ∀ I, IsClosed (U I : Set G))
    (hfl : ∀ I, ParabolicFiniteLength.{uG, max uG uV} (h I) (hU I))
    (hcof : CompactOpenCofinal G)
    (hc : ContragredientPreservesFiniteLength.{uG, max uG uV} G) : Prop :=
  (alternatingOperator P M U h hU hfl).comp (contragredientK0 G hcof hc) =
    (contragredientK0 G hcof hc).comp (alternatingOperator P M U h hU hfl)

end Langlands.Aubert.General
