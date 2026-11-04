import Langlands.Representation.Aubert.General.AssociatedLeviSurvivingStep
import Langlands.Representation.Aubert.General.AssociatedLeviSupport
import Langlands.Representation.Aubert.General.CorrectedOrbitJacquetNatural
import Langlands.Representation.Aubert.General.TerminalJacquet

/-! The associated-Levi comparison at the inverse longest representative. -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Aubert.General.JacquetComplex

open CategoryTheory Langlands.Group.RelativeWeylIndexing
open scoped NNReal

universe uI uG uV

variable {ι : Type uI} [LinearOrder ι] [Fintype ι]
variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable (P M U : Finset ι → Subgroup G)
  (h : ∀ J, IsSemidirectDecomposition (P J) (M J) (U J))
  (hclosed : ∀ J, IsClosed (U J : Set G))
  (hδ : ∀ J, IsUnimodularModulus (U J) (hclosed J))
  (hP : Monotone P) (hU : Antitone U)
variable (T : Subgroup G) [Fintype (Group.RelativeWeyl.Weyl T)]
  [DecidableEq (Group.RelativeWeyl.Weyl T)]
variable {Mx : CoxeterMatrix ι} (cs : CoxeterSystem Mx (Group.RelativeWeyl.Weyl T))
variable [SigmaCompactSpace G] [T2Space G]
  [∀ J, CompactSpace (Induction.LeftQuotient (P J))]
  (hPc : ∀ J, IsClosed (P J : Set G))

include hPc in
/-- The associated-Levi comparison for `I' = associatedSubset cs I` and an element
`n` conjugating `M_I` to `M_{I'}`, at the grade of `w = (longestRep cs I)⁻¹` and
the coordinate `S \ I'`. The orbit Jacquet data are the natural ones of
`naturalOrbitJacquetData`; the remaining inputs are the Bruhat cover, graded
exactness above that grade, the surviving-support hypotheses at that grade, and
the structural facts `S1`, `S2`, `D07` and continuity of the Levi projection. -/
theorem associatedLeviComparison_of_longestRep
    (C : ObjectProperty (SmoothRep.{0, uG, max uI uG uV} ℂ G)) (I : Finset ι)
    (hUc : Jacquet.Localization.IsLimitOfCompactSubgroups (U I)) (n : G)
    (hK : ∀ x : G, x ∈ M I ↔ n⁻¹ * x * n ∈ M (associatedSubset cs I))
    (hMK : IsClosed (M (associatedSubset cs I) : Set G))
    (hLeviK : ∀ L : Finset (associatedSubset cs I),
      IsSemidirectDecomposition ((P (leviIndex (associatedSubset cs I) L)).subgroupOf
          (M (associatedSubset cs I)))
        ((M (leviIndex (associatedSubset cs I) L)).subgroupOf (M (associatedSubset cs I)))
        ((U (leviIndex (associatedSubset cs I) L)).subgroupOf (M (associatedSubset cs I))))
    (hLeviδK : letI := hMK.locallyCompactSpace
      ∀ L : Finset (associatedSubset cs I),
        IsUnimodularModulus ((U (leviIndex (associatedSubset cs I) L)).subgroupOf
          (M (associatedSubset cs I)))
        ((hclosed (leviIndex (associatedSubset cs I) L)).preimage continuous_subtype_val))
    (hcover : CorrectedFiltration.IsBruhatCover T (P ∅) (P I))
    (hsurj : ∀ E, C E → ∀ k, k + 1 = Complex.terminalDegree I → ∀ i,
      CorrectedFiltration.associatedGrade cs I < i →
      i < (Support.rankOrderedList cs.length).length →
      Function.Surjective
        (gradedDifferential.{uI, uG, max uI uV} P M U h hclosed hδ hP hU T cs E I i k))
    (hinj : ∀ E, C E → Complex.terminalDegree I = 1 → ∀ i,
      CorrectedFiltration.associatedGrade cs I < i →
      i < (Support.rankOrderedList cs.length).length →
      Function.Injective
        (gradedDifferential.{uI, uG, max uI uV} P M U h hclosed hδ hP hU T cs E I i 0))
    (hex : ∀ E, C E → ∀ k, k + 2 = Complex.terminalDegree I → ∀ i,
      CorrectedFiltration.associatedGrade cs I < i →
      i < (Support.rankOrderedList cs.length).length →
      LinearMap.range
          (gradedDifferential.{uI, uG, max uI uV} P M U h hclosed hδ hP hU T cs E I i k) =
        LinearMap.ker
          (gradedDifferential.{uI, uG, max uI uV} P M U h hclosed hδ hP hU T cs E I i (k + 1)))
    (H : CorrectedFiltration.SurvivingSupportHypotheses P T cs I
      (CorrectedFiltration.associatedCoordinate cs I).1
      (CorrectedFiltration.associatedGrade cs I) n)
    (hNc : Jacquet.Localization.IsLimitOfCompactSubgroups ((U I).subgroupOf (P I)))
    (hS1 : ∀ s, associatedSubset cs I ⊆ Finset.univ \ s →
      IsMinimal cs (Finset.univ \ s) I (longestRep cs I)⁻¹ →
      ∀ x ∈ U I, n⁻¹ * x * n ∈ P (Finset.univ \ s) → n⁻¹ * x * n ∈ U (associatedSubset cs I))
    (hS2 : ∀ s, associatedSubset cs I ⊆ Finset.univ \ s →
      IsMinimal cs (Finset.univ \ s) I (longestRep cs I)⁻¹ →
      ∀ x ∈ M (Finset.univ \ s), x ∈ U (associatedSubset cs I) → n * x * n⁻¹ ∈ U I)
    (hr : Continuous (h I).projection)
    (hD07 : ∀ l : M I,
      (HaarModulus.closedRestrictCharacter (U I) (hclosed I) (M I) (h I).levi_le_normalizer l :
          ℝ≥0) *
          (HaarModulus.closedRestrictCharacter (U (associatedSubset cs I))
            (hclosed (associatedSubset cs I)) (M (associatedSubset cs I))
            (h (associatedSubset cs I)).levi_le_normalizer (conjugationEquiv n hK l) : ℝ≥0) =
        (HaarModulus.closedRestrictCharacter
            (CorrectedFiltration.orbitUnipotentIntersection (U I) (U (associatedSubset cs I)) n)
            (CorrectedFiltration.isClosed_orbitUnipotentIntersection (hclosed I)
              (hclosed (associatedSubset cs I)) n) (M I)
            (CorrectedFiltration.levi_le_normalizer_orbitUnipotentIntersection (h I)
              (h (associatedSubset cs I)) n hK) l : ℝ≥0) ^ 2) :
    Nonempty ((C.ι ⋙ StandardComplex.sharpFunctor.{uI, uG, max uI uV}
          P M U h hclosed hδ hP hU I ⋙ jacquetFunctor.{uG, max uI uG uV} (h I) (hclosed I)) ≅
        (C.ι ⋙ jacquetFunctor.{uG, max uI uG uV} (h (associatedSubset cs I))
            (hclosed (associatedSubset cs I)) ⋙
          LeviComplex.sharpFunctor.{uI, uG, uV} P M U hclosed hP hU (associatedSubset cs I) hMK
            hLeviK hLeviδK Finset.univ ⋙
          conjugationFunctor.{uG, max uI uG uV} n hK)) :=
  associatedLeviComparison_of_survivingStep.{uI, uG, uV} P M U h hclosed hδ hP hU T cs hPc C I
    hUc (CorrectedFiltration.associatedCoordinate cs I) (CorrectedFiltration.associatedGrade cs I)
    hK hMK hLeviK hLeviδK hcover (CorrectedFiltration.modifiedSupport_lower_eq_empty cs I)
    (CorrectedFiltration.modifiedSupport_other_eq_empty cs I)
    (CorrectedFiltration.length_rankOrderedList_le_associatedGrade_succ cs I) hsurj hinj hex H
    hNc
    (fun X => CorrectedFiltration.naturalOrbitJacquetData.{uI, uG, max uI uV} h hclosed hU hP hPc
      T cs I (longestRep cs I)⁻¹ n (associatedSubset cs I) hK hS1 hS2 hr hD07 hNc (C.ι.obj X))
    (fun f => CorrectedFiltration.naturalOrbitJacquetData_isNatural.{uI, uG, max uI uV} h hclosed
      hU hP hPc T cs I (longestRep cs I)⁻¹ n (associatedSubset cs I) hK hS1 hS2 hr hD07 hNc
      (C.ι.map f))
    (CorrectedFiltration.associatedSubset_subset_associatedCoordinate cs I)
    (CorrectedFiltration.isMinimal_associatedCoordinate cs I)
    (CorrectedFiltration.modifiedSupport_associatedCoordinate_eq_empty cs I)

end Langlands.Aubert.General.JacquetComplex

namespace Langlands.Aubert.General.TerminalJacquet

open CategoryTheory Langlands.Group Langlands.Group.RelativeWeylIndexing
open scoped NNReal

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

/-- The associated-Levi comparison statement (**) for a standard family, from the
Bruhat cover, graded exactness above the grade of the inverse longest
representative on the support category, the surviving-support hypotheses at that
grade for every lift, and the structural facts `S1`, `S2`, `D07` and continuity of
the Levi projections. -/
theorem associatedLeviComparisonStatement_of_inputs
    (hPtop : P Finset.univ = ⊤) (hUtop : U Finset.univ = ⊥)
    (T : Subgroup G) [Fintype (RelativeWeyl.Weyl T)] [DecidableEq (RelativeWeyl.Weyl T)]
    {CM : CoxeterMatrix ι} (actual : ActualCoxeterSystem T CM)
    (hAssociated : actualAssociatedLeviConjugation T M actual)
    [SigmaCompactSpace G] [T2Space G] [∀ J, CompactSpace (Induction.LeftQuotient (P J))]
    (hPc : ∀ J, IsClosed (P J : Set G))
    (hUc : ∀ I, Jacquet.Localization.IsLimitOfCompactSubgroups (U I))
    (hNc : ∀ I, Jacquet.Localization.IsLimitOfCompactSubgroups ((U I).subgroupOf (P I)))
    (hr : ∀ I, Continuous (h I).projection)
    (hcover : ∀ I, CorrectedFiltration.IsBruhatCover T (P ∅) (P I))
    (hsurj : ∀ I E, supportObjects.{uI, uG, uV} P M U h hclosed IsAssociate hM hLevi I E →
      ∀ k, k + 1 = Complex.terminalDegree I → ∀ i,
      CorrectedFiltration.associatedGrade actual I < i →
      i < (Support.rankOrderedList actual.length).length →
      Function.Surjective (JacquetComplex.gradedDifferential.{uI, uG, max uI uV}
        P M U h hclosed hδ hP hU T actual E I i k))
    (hinj : ∀ I E, supportObjects.{uI, uG, uV} P M U h hclosed IsAssociate hM hLevi I E →
      Complex.terminalDegree I = 1 → ∀ i,
      CorrectedFiltration.associatedGrade actual I < i →
      i < (Support.rankOrderedList actual.length).length →
      Function.Injective (JacquetComplex.gradedDifferential.{uI, uG, max uI uV}
        P M U h hclosed hδ hP hU T actual E I i 0))
    (hex : ∀ I E, supportObjects.{uI, uG, uV} P M U h hclosed IsAssociate hM hLevi I E →
      ∀ k, k + 2 = Complex.terminalDegree I → ∀ i,
      CorrectedFiltration.associatedGrade actual I < i →
      i < (Support.rankOrderedList actual.length).length →
      LinearMap.range (JacquetComplex.gradedDifferential.{uI, uG, max uI uV}
          P M U h hclosed hδ hP hU T actual E I i k) =
        LinearMap.ker (JacquetComplex.gradedDifferential.{uI, uG, max uI uV}
          P M U h hclosed hδ hP hU T actual E I i (k + 1)))
    (H : ∀ (I : Finset ι) (n : RelativeWeyl.normalizer T),
      QuotientGroup.mk n = longestRep actual I →
      CorrectedFiltration.SurvivingSupportHypotheses P T actual I
        (CorrectedFiltration.associatedCoordinate actual I).1
        (CorrectedFiltration.associatedGrade actual I) (n : G))
    (hS1 : ∀ (I : Finset ι) (n : RelativeWeyl.normalizer T),
      QuotientGroup.mk n = longestRep actual I →
      ∀ s, associatedSubset actual I ⊆ Finset.univ \ s →
      IsMinimal actual (Finset.univ \ s) I (longestRep actual I)⁻¹ →
      ∀ x ∈ U I, (n : G)⁻¹ * x * (n : G) ∈ P (Finset.univ \ s) →
        (n : G)⁻¹ * x * (n : G) ∈ U (associatedSubset actual I))
    (hS2 : ∀ (I : Finset ι) (n : RelativeWeyl.normalizer T),
      QuotientGroup.mk n = longestRep actual I →
      ∀ s, associatedSubset actual I ⊆ Finset.univ \ s →
      IsMinimal actual (Finset.univ \ s) I (longestRep actual I)⁻¹ →
      ∀ x ∈ M (Finset.univ \ s), x ∈ U (associatedSubset actual I) →
        (n : G) * x * (n : G)⁻¹ ∈ U I)
    (hD07 : ∀ (I : Finset ι) (n : RelativeWeyl.normalizer T),
      QuotientGroup.mk n = longestRep actual I →
      ∀ (hK : ∀ x : G, x ∈ M I ↔ (n : G)⁻¹ * x * (n : G) ∈ M (associatedSubset actual I))
        (l : M I),
      (HaarModulus.closedRestrictCharacter (U I) (hclosed I) (M I) (h I).levi_le_normalizer l :
          ℝ≥0) *
          (HaarModulus.closedRestrictCharacter (U (associatedSubset actual I))
            (hclosed (associatedSubset actual I)) (M (associatedSubset actual I))
            (h (associatedSubset actual I)).levi_le_normalizer
            (conjugationEquiv (n : G) hK l) : ℝ≥0) =
        (HaarModulus.closedRestrictCharacter
            (CorrectedFiltration.orbitUnipotentIntersection (U I)
              (U (associatedSubset actual I)) (n : G))
            (CorrectedFiltration.isClosed_orbitUnipotentIntersection (hclosed I)
              (hclosed (associatedSubset actual I)) (n : G)) (M I)
            (CorrectedFiltration.levi_le_normalizer_orbitUnipotentIntersection (h I)
              (h (associatedSubset actual I)) (n : G) hK) l : ℝ≥0) ^ 2) :
    AssociatedLeviComparisonStatement.{uI, uG, uV} P M U h hclosed hδ hP hU IsAssociate hM
      hLevi hLeviδ hPtop hUtop T actual hAssociated := by
  intro I n hn I' hnM C
  exact JacquetComplex.associatedLeviComparison_of_longestRep.{uI, uG, uV} P M U h hclosed hδ
    hP hU T actual hPc C I (hUc I) (n : G) hnM (hM I') (hLevi I') (hLeviδ I') (hcover I)
    (hsurj I) (hinj I) (hex I) (H I n hn) (hNc I) (hS1 I n hn) (hS2 I n hn) (hr I)
    (hD07 I n hn hnM)

end Langlands.Aubert.General.TerminalJacquet
