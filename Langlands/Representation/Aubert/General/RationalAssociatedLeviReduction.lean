import Langlands.Representation.Aubert.General.AssociatedLeviLongestRep
import Langlands.Representation.Aubert.General.RationalTerminalJacquet
import Langlands.Representation.Aubert.General.RationalCorrectedSurvivingSupportTarget
import Langlands.Representation.Aubert.General.RationalCorrectedOrbitRadicalTarget
import Langlands.Representation.Aubert.General.RationalCorrectedOrbitModulusTarget
import Langlands.Representation.Aubert.General.RationalCorrectedGradedReduction
import Langlands.Representation.Aubert.General.RationalInductionDualityReduction
import Langlands.Representation.Aubert.General.RationalWeylComparisonTarget
import Langlands.GroupScheme.Rational.Statement
import Langlands.Representation.Aubert.General.CorrectedGradedTopSurjectivity
import Langlands.Representation.Aubert.General.AssociatedLeviDescent

/-! # The rational associated-Levi comparison from published rational inputs

`AssociatedGradedExactnessTarget` is the graded-exactness input of
`TerminalJacquet.associatedLeviComparisonStatement_of_inputs`: on the support
category of `L_I`, the associated graded maps of the corrected support filtration
are exact above the grade of `(longestRep I)⁻¹`, in the three degree ranges used
by the cokernel argument. `RationalAssociatedGradedExactnessStatement` is its
rational-point instance. The theorem
`rationalAssociatedLeviComparisonStatement_of_inputs` proves the exact
`RationalAssociatedLeviComparisonStatement` from this statement and five
published rational propositions: the rational Bruhat decomposition, quotient
compactness of dynamic parabolics, the surviving-support statement and the two
orbit statements. `rationalAssociatedGradedExactnessStatement_of_targets` derives
the graded-exactness statement from the published graded vanishing and transition
statements, so `rationalAssociatedLeviComparisonStatement_of_published` proves the
target from seven published rational propositions. No inhabitant of any input is
constructed.
-/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Aubert.General.TerminalJacquet

open CategoryTheory Langlands.Group Langlands.Group.RelativeWeylIndexing

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

/-- Graded exactness above the associated grade on the support category of `L_I`:
for every `E` in it and every grade `i` with `associatedGrade I < i`, the associated
graded map of the actual degree filtration of `r_I` of the complex of `E` is
surjective into the terminal degree, injective in degree `0` when the terminal
degree is `1`, and exact at every degree `k + 1` with `k + 2` the terminal degree.
This is a proposition template, not an assertion for arbitrary families. -/
def AssociatedGradedExactnessTarget (T : Subgroup G) [Fintype (RelativeWeyl.Weyl T)]
    [DecidableEq (RelativeWeyl.Weyl T)] {CM : CoxeterMatrix ι}
    (actual : ActualCoxeterSystem T CM) : Prop :=
  ∀ I E, supportObjects.{uI, uG, uV} P M U h hclosed IsAssociate hM hLevi I E →
    (∀ k, k + 1 = Complex.terminalDegree I → ∀ i,
      CorrectedFiltration.associatedGrade actual I < i →
      i < (Support.rankOrderedList actual.length).length →
      Function.Surjective (JacquetComplex.gradedDifferential.{uI, uG, max uI uV}
        P M U h hclosed hδ hP hU T actual E I i k)) ∧
    (Complex.terminalDegree I = 1 → ∀ i,
      CorrectedFiltration.associatedGrade actual I < i →
      i < (Support.rankOrderedList actual.length).length →
      Function.Injective (JacquetComplex.gradedDifferential.{uI, uG, max uI uV}
        P M U h hclosed hδ hP hU T actual E I i 0)) ∧
    (∀ k, k + 2 = Complex.terminalDegree I → ∀ i,
      CorrectedFiltration.associatedGrade actual I < i →
      i < (Support.rankOrderedList actual.length).length →
      LinearMap.range (JacquetComplex.gradedDifferential.{uI, uG, max uI uV}
          P M U h hclosed hδ hP hU T actual E I i k) =
        LinearMap.ker (JacquetComplex.gradedDifferential.{uI, uG, max uI uV}
          P M U h hclosed hδ hP hU T actual E I i (k + 1)))

/-- The graded vanishing and transition targets and the actual Levi Weyl
identification give graded exactness above the associated grade. Surjectivity
uses that the associated grade carries `(longestRep I)⁻¹`, whose left descents
are `S \ I'` with `W_{I'} = w W_I w⁻¹`. -/
theorem associatedGradedExactnessTarget_of_targets (T : Subgroup G)
    [Fintype (RelativeWeyl.Weyl T)] [DecidableEq (RelativeWeyl.Weyl T)]
    {CM : CoxeterMatrix ι} (actual : ActualCoxeterSystem T CM)
    (hvan : CorrectedFiltration.CorrectedGradedVanishingTarget.{uI, uG, max uI uV}
      P M U h hclosed hM hLevi IsAssociate T actual)
    (htrans : CorrectedFiltration.CorrectedGradedTransitionTarget.{uI, uG, max uI uV}
      P M U h hclosed hδ hP hU hM hLevi IsAssociate T actual)
    (hW : actualLeviWeylIdentification T M actual) :
    AssociatedGradedExactnessTarget.{uI, uG, uV} P M U h hclosed hδ hP hU IsAssociate hM
      hLevi T actual := by
  intro I E hE
  refine ⟨?_, ?_, ?_⟩
  · exact JacquetComplex.gradedDifferential_surjective_top_of_leftDescentSet_eq hvan htrans hW
      hE (CorrectedFiltration.associatedGrade_lt actual I)
      (CorrectedFiltration.mem_standardSubgroup_associatedSubset_iff_rankOrderedElement actual I)
      (CorrectedFiltration.length_lt_rankOrderedElement_associatedGrade_mul_simple actual I)
      (CorrectedFiltration.leftDescentSet_rankOrderedElement_associatedGrade actual I)
  · intro h1 i _ hi
    refine JacquetComplex.gradedDifferential_injective_zero hvan htrans hW hE hi ?_
    unfold Complex.terminalDegree at h1
    omega
  · intro k hk i _ hi
    refine JacquetComplex.gradedDifferential_range_eq_ker hvan htrans hW hE hi k ?_
    unfold Complex.terminalDegree at hk
    omega

end Langlands.Aubert.General.TerminalJacquet

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Group.RelativeWeylIndexing

section Bruhat

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- The rational Bruhat decomposition, the minimal endpoint `P_∅(k) = P(ν)(k)` and
the order of the standard parabolics give `G(k) = ⋃ P_∅ n P_I` over the actual
normalizer of the torus image. -/
theorem isBruhatCover_standard (hBr : RationalBruhatStatement.{u})
    (hEndpoints : StandardParabolicEndpointsStatement.{u})
    (hOrder : StandardParabolicOrderStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (I : Finset (SimpleRoot i ν)) :
    CorrectedFiltration.IsBruhatCover (torusPoints i) (parabolic i ν ∅)
      (parabolic i ν I) := by
  have hempty : parabolic i ν ∅ =
      (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)) := by
    have := hi.isSplitSubtorus.mono
    change (standardParabolic i ν (rootSet i ν ∅)).carrier _ = _
    rw [rootSet_empty, (hEndpoints k G hG T i hi ν hν).1]
  intro g
  obtain ⟨n, hn, p, hp, q, hq, rfl⟩ := (hBr k G hG T i hi ν hν).1 g
  refine ⟨⟨n, normalizerPoints_le_pointNormalizer i hn⟩, p, hempty ▸ hp, q,
    standardParabolic_monotone i ν hOrder hG hi hν (Finset.empty_subset I) (hempty ▸ hq), rfl⟩

end Bruhat

/-- The rational instance of `AssociatedGradedExactnessTarget`, under the
premises of `RationalCorrectedGradedTransitionStatement`. No proof is supplied. -/
def RationalAssociatedGradedExactnessStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    ∀ [LocallyCompactSpace (RationalPoint k G.X)]
      [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
      (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
      (hStandard : StandardCocharacterStatement.{u})
      (hOrder : StandardParabolicOrderStatement.{u})
      (hInter : StandardLeviIntersectionStatement.{u})
      (hRoots : HasRelativeRootSystem i)
      (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
      (hM : ∀ I, IsClosed (levi i ν I : Set (RationalPoint k G.X)))
      (hUc : ∀ I, Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν I)),
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      ∀ [LinearOrder (SimpleRoot i ν)] [Fintype (Weyl i)],
      letI : DecidableEq (Weyl i) := Classical.decEq _
      ∀ (CM : CoxeterMatrix (SimpleRoot i ν))
        (cs : ActualCoxeterSystem (torusPoints i) CM),
        RootLengthComparison i ν hN hZ cs →
        PositiveSimpleReflectionComparison i ν hN hZ cs →
        actualLeviWeylIdentification (torusPoints i) (levi i ν) cs →
        TerminalJacquet.AssociatedGradedExactnessTarget.{u, u, max (u + 1) v}
          (parabolic i ν) (levi i ν) (unipotent i ν)
          (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν)
          hU (standardUnipotent_isUnimodular i ν hU hUc)
          (standardParabolic_monotone i ν hOrder hG hi hν)
          (standardUnipotent_antitone i ν hOrder hG hi hν)
          (rootAssociation i ν hN hZ) hM
          (isSemidirectDecomposition_in_levi i ν hInter hG hi hν)
          (torusPoints i) cs

/-- The published rational graded vanishing and transition statements prove
`RationalAssociatedGradedExactnessStatement`. -/
theorem rationalAssociatedGradedExactnessStatement_of_targets
    (hvan : RationalCorrectedGradedVanishingStatement.{u, v})
    (htrans : RationalCorrectedGradedTransitionStatement.{u, v}) :
    RationalAssociatedGradedExactnessStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hOrder hInter hRoots hN hZ hU hM hUc
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  intro _ _
  let : DecidableEq (Weyl i) := Classical.decEq _
  intro CM cs hlen hpos hlevi
  exact TerminalJacquet.associatedGradedExactnessTarget_of_targets
    (parabolic i ν) (levi i ν) (unipotent i ν)
    (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν) hU
    (standardUnipotent_isUnimodular i ν hU hUc)
    (standardParabolic_monotone i ν hOrder hG hi hν)
    (standardUnipotent_antitone i ν hOrder hG hi hν)
    (rootAssociation i ν hN hZ) hM
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν) (torusPoints i) cs
    (hvan k G hG T i hi ν hν hStandard hInter hRoots hN hZ hU hM CM cs hlen hpos hlevi)
    (htrans k G hG T i hi ν hν hStandard hOrder hInter hRoots hN hZ hU hM hUc CM cs hlen hpos
      hlevi)
    hlevi

/-- The exact `RationalAssociatedLeviComparisonStatement` from the rational Bruhat
decomposition, quotient compactness of dynamic parabolics, the surviving-support
and orbit statements, and graded exactness above the associated grade. -/
theorem rationalAssociatedLeviComparisonStatement_of_inputs
    (hBr : RationalBruhatStatement.{u})
    (hcompact : Langlands.BruhatTits.DynamicParabolicQuotientCompactStatement.{u})
    (hsupp : RationalCorrectedSurvivingSupportStatement.{u})
    (hrad : RationalCorrectedOrbitRadicalIntersectionStatement.{u})
    (hmod : RationalCorrectedOrbitSquaredModulusStatement.{u})
    (hgr : RationalAssociatedGradedExactnessStatement.{u, v}) :
    RationalAssociatedLeviComparisonStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hOrder hEndpoints hInter hRoots hN hZ hU hM hUc hUcLevi
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  intro _ _ CM actual hlen hpos hlevi _ _ hAssociated
  let : DecidableEq (Weyl i) := Classical.decEq _
  have : SecondCountableTopology (RationalPoint k G.X) :=
    reductiveRationalPoint_secondCountable k G hG
  have : SigmaCompactSpace (RationalPoint k G.X) :=
    sigmaCompactSpace_of_locallyCompact_secondCountable
  have : ∀ J, CompactSpace (Induction.LeftQuotient (parabolic i ν J)) := fun J =>
    compactSpace_leftQuotient_parabolic i ν hcompact hStandard hG hi hν J
  have hPc : ∀ J, IsClosed (parabolic i ν J : Set (RationalPoint k G.X)) := fun J =>
    isClosed_standard_parabolic i ν hStandard hG hi hν J
  have hr : ∀ I, Continuous
      (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν
        I).projection := fun I =>
    continuous_standard_projection i ν hStandard hG hi hν I
  have hNc : ∀ I, Jacquet.Localization.IsLimitOfCompactSubgroups
      ((unipotent i ν I).subgroupOf (parabolic i ν I)) := fun I =>
    isLimitOfCompactSubgroups_subgroupOf (unipotent i ν I) (parabolic i ν I) (hPc I) (hUc I)
  have hS := hsupp k G hG T i hi ν hν hStandard hOrder hInter hRoots hN hZ hU hM hUc CM
    actual hlen hpos hlevi
  have hR := hrad k G hG T i hi ν hν hStandard hOrder hInter hRoots hN hZ hU hM hUc CM
    actual hlen hpos hlevi
  have hD := hmod k G hG T i hi ν hν hStandard hOrder hInter hRoots hN hZ hU hM hUc CM
    actual hlen hpos hlevi
  have hE := hgr k G hG T i hi ν hν hStandard hOrder hInter hRoots hN hZ hU hM hUc CM
    actual hlen hpos hlevi
  have hlift : ∀ (I : Finset (SimpleRoot i ν)) (n : Group.RelativeWeyl.normalizer (torusPoints i)),
      QuotientGroup.mk n = longestRep actual I →
      (QuotientGroup.mk n : Weyl i) =
        (Support.rankOrderedElement actual.length (CorrectedFiltration.associatedGrade actual I)
          (CorrectedFiltration.associatedGrade_lt actual I))⁻¹ := by
    intro I n hn
    rw [CorrectedFiltration.rankOrderedElement_associatedGrade, inv_inv]
    exact hn
  have hconj : ∀ (I : Finset (SimpleRoot i ν)) (n : Group.RelativeWeyl.normalizer (torusPoints i)),
      QuotientGroup.mk n = longestRep actual I →
      ∀ x : RationalPoint k G.X, x ∈ levi i ν I ↔
        (n : RationalPoint k G.X)⁻¹ * x * (n : RationalPoint k G.X) ∈
          levi i ν (associatedSubset actual I) := by
    intro I n hn x
    rw [← hAssociated I n hn, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hy
    · intro hx
      exact ⟨(n : RationalPoint k G.X)⁻¹ * x * (n : RationalPoint k G.X), hx,
        by simp [MulAut.conj_apply, mul_assoc]⟩
  refine TerminalJacquet.associatedLeviComparisonStatement_of_inputs.{u, u, max (u + 1) v}
    (parabolic i ν) (levi i ν) (unipotent i ν)
    (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν) hU
    (standardUnipotent_isUnimodular i ν hU hUc)
    (standardParabolic_monotone i ν hOrder hG hi hν)
    (standardUnipotent_antitone i ν hOrder hG hi hν)
    (rootAssociation i ν hN hZ) hM
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν)
    (standardLeviUnipotent_isUnimodular i ν hU hM hUcLevi)
    (standardParabolic_univ i ν hEndpoints hG hi hν)
    (standardUnipotent_univ i ν hEndpoints hG hi hν)
    (torusPoints i) actual hAssociated hPc hUc hNc hr
    (fun I => isBruhatCover_standard i ν hBr hEndpoints hOrder hG hi hν I)
    (fun I E hE' => (hE I E hE').1) (fun I E hE' => (hE I E hE').2.1)
    (fun I E hE' => (hE I E hE').2.2) ?_ ?_ ?_ ?_
  · intro I n hn
    have := hS I (CorrectedFiltration.associatedCoordinate actual I).1
      (CorrectedFiltration.associatedGrade actual I)
      (CorrectedFiltration.associatedGrade_lt actual I) n (hlift I n hn)
    rw [CorrectedFiltration.rankOrderedElement_associatedGrade] at this
    exact this (CorrectedFiltration.isMinimal_associatedCoordinate actual I)
  · intro I n hn
    have := (hR I (CorrectedFiltration.associatedGrade actual I)
      (CorrectedFiltration.associatedGrade_lt actual I) n (hlift I n hn)
      (associatedSubset actual I) (hconj I n hn)).1
    rw [CorrectedFiltration.rankOrderedElement_associatedGrade] at this
    exact this
  · intro I n hn
    have := (hR I (CorrectedFiltration.associatedGrade actual I)
      (CorrectedFiltration.associatedGrade_lt actual I) n (hlift I n hn)
      (associatedSubset actual I) (hconj I n hn)).2
    rw [CorrectedFiltration.rankOrderedElement_associatedGrade] at this
    exact this
  · intro I n hn hK
    exact hD I (CorrectedFiltration.associatedGrade actual I)
      (CorrectedFiltration.associatedGrade_lt actual I) n (hlift I n hn)
      (associatedSubset actual I) hK

/-- The exact `RationalAssociatedLeviComparisonStatement` from seven published
rational propositions: the Bruhat decomposition, quotient compactness, the
surviving-support and two orbit statements, and the graded vanishing and
transition statements. -/
theorem rationalAssociatedLeviComparisonStatement_of_published
    (hBr : RationalBruhatStatement.{u})
    (hcompact : Langlands.BruhatTits.DynamicParabolicQuotientCompactStatement.{u})
    (hsupp : RationalCorrectedSurvivingSupportStatement.{u})
    (hrad : RationalCorrectedOrbitRadicalIntersectionStatement.{u})
    (hmod : RationalCorrectedOrbitSquaredModulusStatement.{u})
    (hvan : RationalCorrectedGradedVanishingStatement.{u, v})
    (htrans : RationalCorrectedGradedTransitionStatement.{u, v}) :
    RationalAssociatedLeviComparisonStatement.{u, v} :=
  rationalAssociatedLeviComparisonStatement_of_inputs hBr hcompact hsupp hrad hmod
    (rationalAssociatedGradedExactnessStatement_of_targets hvan htrans)

end Langlands.Aubert.General.RationalPointFamily
