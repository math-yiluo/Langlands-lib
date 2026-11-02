import Langlands.Representation.Aubert.General.AlternatingOperator

/-! # Target for involutivity of the general unadjusted Aubert operator -/

noncomputable section

namespace Langlands.Aubert.General

universe uI uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {ι : Type uI} [Fintype ι]

/-- Aubert Theorem 1.7(3): the square of the unadjusted alternating operator
is the identity on the whole exact finite-length Grothendieck group.
This definition states the target and proves no instance of it. -/
def InvolutivityStatement
    (P M U : Finset ι → Subgroup G)
    (h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I))
    (hU : ∀ I, IsClosed (U I : Set G))
    (hfl : ∀ I, ParabolicFiniteLength.{uG, max uG uV} (h I) (hU I)) : Prop :=
  (alternatingOperator P M U h hU hfl).comp
      (alternatingOperator P M U h hU hfl) =
    LinearMap.id

end Langlands.Aubert.General
