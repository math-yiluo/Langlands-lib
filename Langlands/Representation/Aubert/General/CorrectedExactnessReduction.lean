import Langlands.Representation.Aubert.General.CorrectedGradedExactness
import Langlands.Representation.Aubert.General.JacquetExactness
import Langlands.Representation.Aubert.General.SharpSupportRetentionReduction

/-! # Conditional assembly of corrected exactness on the actual complex -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Aubert.General.JacquetComplex

open CategoryTheory Langlands.Group.RelativeWeylIndexing

universe uI uG uV

variable {ι : Type uI} [LinearOrder ι] [Fintype ι]
variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable (P M U : Finset ι → Subgroup G)
  (h : ∀ J, IsSemidirectDecomposition (P J) (M J) (U J))
  (hclosed : ∀ J, IsClosed (U J : Set G))
  (hδ : ∀ J, IsUnimodularModulus (U J) (hclosed J))
  (hP : Monotone P) (hU : Antitone U)
  (hM : ∀ I, IsClosed (M I : Set G))
  (hL : ∀ (I : Finset ι) (K : Finset I),
    IsSemidirectDecomposition ((P (leviIndex I K)).subgroupOf (M I))
      ((M (leviIndex I K)).subgroupOf (M I)) ((U (leviIndex I K)).subgroupOf (M I)))
  (IsAssociate : Finset ι → Finset ι → G → Prop)

/-- Induction--Jacquet stability places every homogeneous object of the actual
complex in the same support category as its input. -/
theorem degreeObject_isInSupportCategory
    (hIJ : SupportCategoryInductionJacquetTarget.{uI, uG, max uI uV}
      P M U h hclosed hM hL IsAssociate)
    (A : SmoothRep.{0, uG, max uI uG uV} ℂ G) (I : Finset ι)
    (hA : IsInSupportCategory.{uI, uG, max uI uV}
      P M U h hclosed IsAssociate I (hM I) (hL I) A)
    (k : ℕ) :
    IsInSupportCategory.{uI, uG, max uI uV} P M U h hclosed IsAssociate I (hM I) (hL I)
      (StandardComplex.degreeObject.{uI, uG, max uI uV} P M U h hclosed A k) :=
  IsInSupportCategory.of_jointlyInjective
    (StandardComplex.degreeProjection P M U h hclosed A k)
    (StandardComplex.degreeProjection_jointlyInjective P M U h hclosed A k)
    (fun s => hIJ I (Finset.univ \ s.1) A hA)

variable (T : Subgroup G) [Fintype (Group.RelativeWeyl.Weyl T)]
  [DecidableEq (Group.RelativeWeyl.Weyl T)]
  {CM : CoxeterMatrix ι} (cs : ActualCoxeterSystem T CM)

/-- The explicit structural inputs for the corrected-exactness reduction.
This data type supplies no inhabitant of any of its fields. -/
structure CorrectedExactnessInputs where
  gradedVanishing : CorrectedFiltration.CorrectedGradedVanishingTarget.{uI, uG, max uI uV}
    P M U h hclosed hM hL IsAssociate T cs
  gradedTransition : CorrectedFiltration.CorrectedGradedTransitionTarget.{uI, uG, max uI uV}
    P M U h hclosed hδ hP hU hM hL IsAssociate T cs
  leviWeyl : actualLeviWeylIdentification T M cs
  associationCard : ∀ (I J : Finset ι) (n : G), IsAssociate I J n →
    (∀ x : G, x ∈ M J ↔ n⁻¹ * x * n ∈ M I) → J.card = I.card
  associationSupport : SupportCategoryAssociationInvarianceTarget.{uI, uG, max uI uV}
    P M U h hclosed hM hL IsAssociate
  bruhatCover : ∀ J, CorrectedFiltration.IsBruhatCover T (P ∅) (P J)
  inductionJacquet : SupportCategoryInductionJacquetTarget.{uI, uG, max uI uV}
    P M U h hclosed hM hL IsAssociate
  exactnessDetection : SupportCategoryExactnessDetectionTarget.{uI, uG, max uI uV}
    P M U h hclosed hM hL IsAssociate

/-- The two graded targets, actual Levi Weyl comparison, Bruhat cover,
association invariance, induction--Jacquet stability and Jacquet detection
together imply exactness of the actual complex before its retained terminal
degree. Every one of these structural premises is explicit. -/
theorem isExactBeforeTerminal_of_correctedTargets
    (hvan : CorrectedFiltration.CorrectedGradedVanishingTarget.{uI, uG, max uI uV}
      P M U h hclosed hM hL IsAssociate T cs)
    (htrans : CorrectedFiltration.CorrectedGradedTransitionTarget.{uI, uG, max uI uV}
      P M U h hclosed hδ hP hU hM hL IsAssociate T cs)
    (hLevi : actualLeviWeylIdentification T M cs)
    (hcard : ∀ (I J : Finset ι) (n : G), IsAssociate I J n →
      (∀ x : G, x ∈ M J ↔ n⁻¹ * x * n ∈ M I) → J.card = I.card)
    (hassoc : SupportCategoryAssociationInvarianceTarget.{uI, uG, max uI uV}
      P M U h hclosed hM hL IsAssociate)
    (hcover : ∀ J, CorrectedFiltration.IsBruhatCover T (P ∅) (P J))
    (hIJ : SupportCategoryInductionJacquetTarget.{uI, uG, max uI uV}
      P M U h hclosed hM hL IsAssociate)
    (hdetect : SupportCategoryExactnessDetectionTarget.{uI, uG, max uI uV}
      P M U h hclosed hM hL IsAssociate)
    (A : SmoothRep.{0, uG, max uI uG uV} ℂ G) (I : Finset ι)
    (hA : IsInSupportCategory.{uI, uG, max uI uV}
      P M U h hclosed IsAssociate I (hM I) (hL I) A) :
    StandardComplex.IsExactBeforeTerminal.{uI, uG, max uI uV}
      P M U h hclosed hδ hP hU A I := by
  have hsupp (J : Finset ι) (n : G) (hn : IsAssociate I J n)
      (hconj : ∀ x : G, x ∈ M J ↔ n⁻¹ * x * n ∈ M I) :
      IsInSupportCategory P M U h hclosed IsAssociate J (hM J) (hL J) A :=
    hassoc I J n hn hconj A hA
  exact isExactBeforeTerminal_of_jacquet P M U h hclosed hδ hP hU hM hL IsAssociate
    hdetect A I
    (fun k _ => degreeObject_isInSupportCategory P M U h hclosed hM hL IsAssociate
      hIJ A I hA k)
    (associated_degreeDifferential_injective_zero_of_targets hvan htrans hLevi
      (hcard I) hsupp (fun J _ _ _ => hcover J))
    (associated_degreeDifferential_exact_of_targets hvan htrans hLevi
      (hcard I) hsupp (fun J _ _ _ => hcover J))

/-- Consume the explicit input data without adding any structural hypothesis. -/
theorem isExactBeforeTerminal_of_inputs
    (H : CorrectedExactnessInputs.{uI, uG, uV}
      P M U h hclosed hδ hP hU hM hL IsAssociate T cs)
    (A : SmoothRep.{0, uG, max uI uG uV} ℂ G) (I : Finset ι)
    (hA : IsInSupportCategory.{uI, uG, max uI uV}
      P M U h hclosed IsAssociate I (hM I) (hL I) A) :
    StandardComplex.IsExactBeforeTerminal.{uI, uG, max uI uV}
      P M U h hclosed hδ hP hU A I :=
  isExactBeforeTerminal_of_correctedTargets.{uI, uG, uV}
    P M U h hclosed hδ hP hU hM hL IsAssociate T cs
    H.gradedVanishing H.gradedTransition H.leviWeyl H.associationCard H.associationSupport
    H.bruhatCover H.inductionJacquet H.exactnessDetection A I hA

end Langlands.Aubert.General.JacquetComplex
