import Langlands.Representation.Aubert.General.LeviComplex
import Langlands.Representation.Aubert.General.SupportCategory
import Langlands.Group.RelativeWeylIndexingTargets
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! Full-smooth terminal-cokernel and associated-Levi targets from the erratum. -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Aubert.General.TerminalJacquet

open CategoryTheory Langlands.Group

universe uI uG uV

variable {ι : Type uI} [LinearOrder ι] [Fintype ι]
variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable (P M U : Finset ι → Subgroup G)
variable (h : ∀ J, IsSemidirectDecomposition (P J) (M J) (U J))
variable (hclosed : ∀ J, IsClosed (U J : Set G))
variable (hδ : ∀ J, IsUnimodularModulus (U J) (hclosed J))
variable (hP : Monotone P) (hU : Antitone U)
variable (IsAssociate : Finset ι → Finset ι → G → Prop)
variable (hM : ∀ J, IsClosed (M J : Set G))
variable (hLevi : ∀ (J : Finset ι) (K : Finset J),
  IsSemidirectDecomposition ((P (leviIndex J K)).subgroupOf (M J))
    ((M (leviIndex J K)).subgroupOf (M J))
    ((U (leviIndex J K)).subgroupOf (M J)))
variable (hLeviδ : ∀ J, letI := (hM J).locallyCompactSpace
  ∀ K : Finset J, IsUnimodularModulus ((U (leviIndex J K)).subgroupOf (M J))
    ((hclosed (leviIndex J K)).preimage continuous_subtype_val))

/-- The objects of the full smooth support category, in a universe closed under
the constructed cokernel and induction functors. -/
def supportObjects (I : Finset ι) :
    ObjectProperty (SmoothRep.{0, uG, max uI uG uV} ℂ G) :=
  IsInSupportCategory.{uI, uG, max uI uV}
    P M U h hclosed IsAssociate I (hM I) (hLevi I)

/-- The support-theoretic prerequisite for applying the full-Levi cuspidal
cokernel construction to the Jacquet module in the erratum. -/
def JacquetCuspidalStatement : Prop :=
  ∀ (I : Finset ι) (E : SmoothRep.{0, uG, max uI uG uV} ℂ G),
    supportObjects P M U h hclosed IsAssociate hM hLevi I E →
      IsLeviCuspidal P M U hclosed I (hM I) (hLevi I)
        ((jacquetFunctor (h I) (hclosed I)).obj E)

/-- The fixed-Levi comparison preceding (**) on p.4690, with actual functors
and all equivariant maps in the full smooth support category. -/
def FixedLeviComparisonStatement : Prop :=
  ∀ I : Finset ι,
    let C := supportObjects.{uI, uG, uV} P M U h hclosed IsAssociate hM hLevi I
    Nonempty
      ((C.ι ⋙ jacquetFunctor (h I) (hclosed I) ⋙
          LeviComplex.sharpFunctor P M U hclosed hP hU I
            (hM I) (hLevi I) (hLeviδ I) Finset.univ) ≅
        (C.ι ⋙ jacquetFunctor (h I) (hclosed I)))

/-- The associated-Levi terminal-cokernel comparison (**), on every smooth
object of `Alg({I})`. The Weyl element is the specified longest representative
of `D(I,∅)`, and every lift acts by the actual conjugation functor. -/
def AssociatedLeviComparisonStatement
    (_hPtop : P Finset.univ = ⊤) (_hUtop : U Finset.univ = ⊥)
    (T : Subgroup G) [Fintype (RelativeWeyl.Weyl T)]
    {CM : CoxeterMatrix ι} (actual : RelativeWeylIndexing.ActualCoxeterSystem T CM)
    (hAssociated : RelativeWeylIndexing.actualAssociatedLeviConjugation T M actual) :
    Prop :=
  ∀ (I : Finset ι) (n : RelativeWeyl.normalizer T)
    (hn : QuotientGroup.mk n = RelativeWeylIndexing.longestRep actual I),
    let I' := RelativeWeylIndexing.associatedSubset actual I
    let hnM : ∀ x : G, x ∈ M I ↔ (n : G)⁻¹ * x * (n : G) ∈ M I' := by
      intro x
      rw [← hAssociated I n hn, Subgroup.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa [MulAut.conj_apply, mul_assoc] using hy
      · intro hx
        exact ⟨(n : G)⁻¹ * x * (n : G), hx,
          by simp [MulAut.conj_apply, mul_assoc]⟩
    let C := supportObjects.{uI, uG, uV} P M U h hclosed IsAssociate hM hLevi I
    Nonempty
      ((C.ι ⋙ StandardComplex.sharpFunctor.{uI, uG, max uI uV}
          P M U h hclosed hδ hP hU I ⋙ jacquetFunctor (h I) (hclosed I)) ≅
        (C.ι ⋙ jacquetFunctor (h I') (hclosed I') ⋙
          LeviComplex.sharpFunctor P M U hclosed hP hU I'
            (hM I') (hLevi I') (hLeviδ I') Finset.univ ⋙
          conjugationFunctor (n : G) hnM))

end Langlands.Aubert.General.TerminalJacquet
