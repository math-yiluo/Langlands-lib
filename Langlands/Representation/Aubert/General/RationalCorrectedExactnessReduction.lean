import Langlands.Representation.Aubert.General.CorrectedExactnessReduction
import Langlands.Representation.Aubert.General.RationalCorrectedTheorem36
import Langlands.Representation.Aubert.General.RationalCorrectedFiltrationTargets
import Langlands.Representation.Aubert.General.RationalSupportAssociationInvariance
import Langlands.Representation.Aubert.General.RootAssociationLaws
import Langlands.Representation.Aubert.General.RationalSuppliedCoxeterComparisons
import Langlands.GroupScheme.Rational.EndpointReductions

/-! # Actual rational corrected exactness from five explicit inputs -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Group.RelativeWeylIndexing

/-- The remaining global inputs to this conditional proof of rational corrected
exactness. No inhabitant of any field is constructed here. -/
structure RationalCorrectedExactnessInputs where
  bruhat : RationalBruhatStatement.{u}
  gradedVanishing : RationalCorrectedGradedVanishingStatement.{u, v}
  gradedTransition : RationalCorrectedGradedTransitionStatement.{u, v}
  inductionJacquet : RationalSupportCategoryInductionJacquetStatement.{u, v}
  exactnessDetection : RationalSupportCategoryExactnessDetectionStatement.{u, v}

section BruhatCover

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- The given standard-cocharacter statement identifies the empty standard
point parabolic with the dynamic parabolic of the defining cocharacter. -/
theorem parabolic_empty_eq_dynamic_of_standardCocharacter
    (hStandard : StandardCocharacterStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) :
    parabolic i ν ∅ =
      (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)) := by
  have heq := (hStandard k G hG T i hi ν hν ∅ (Set.empty_subset _)).2
    ν (isStandardCocharacter_empty_self i ν)
  change (standardParabolic i ν (rootSet i ν ∅)).carrier _ = _
  rw [rootSet_empty, heq.1]

/-- Rational Bruhat covering and the given standard-cocharacter and order
statements give the exact cover used by every corrected support filtration. -/
theorem standardBruhatCover_of_rationalBruhat
    (hStandard : StandardCocharacterStatement.{u})
    (hOrder : StandardParabolicOrderStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hN : HasPointNormalizerComparison i)
    (hBr : HasRationalBruhatDecomposition i ν)
    (J : Finset (SimpleRoot i ν)) :
    CorrectedFiltration.IsBruhatCover (torusPoints i) (parabolic i ν ∅) (parabolic i ν J) := by
  intro g
  obtain ⟨n, hn, p, hp, q, hq, hg⟩ := hBr.1 g
  have hB := parabolic_empty_eq_dynamic_of_standardCocharacter i ν hStandard hG hi hν
  have hpB : p ∈ parabolic i ν ∅ := hB.symm ▸ hp
  have hqB : q ∈ parabolic i ν ∅ := hB.symm ▸ hq
  exact ⟨normalizerEquiv i hN ⟨n, hn⟩, p, hpB, q,
    standardParabolic_monotone i ν hOrder hG hi hν (Finset.empty_subset J) hqB, hg⟩

end BruhatCover

/-- Conditional actual rational exactness without an endpoint-statement
premise. The five global inputs are explicit in `H`. -/
theorem rationalIsExactBeforeTerminal_of_inputs
    (H : RationalCorrectedExactnessInputs.{u, v}) :
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
        ∀ [LinearOrder (SimpleRoot i ν)] (I : Finset (SimpleRoot i ν))
          (E : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X)),
          IsInSupportCategory.{u, u, max (u + 1) v}
            (parabolic i ν) (levi i ν) (unipotent i ν)
            (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν)
            hU (rootAssociation i ν hN hZ) I (hM I)
            (isSemidirectDecomposition_in_levi i ν hInter hG hi hν I) E →
          StandardComplex.IsExactBeforeTerminal.{u, u, max (u + 1) v}
            (parabolic i ν) (levi i ν) (unipotent i ν)
            (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν)
            hU (standardUnipotent_isUnimodular i ν hU hUc)
            (standardParabolic_monotone i ν hOrder hG hi hν)
            (standardUnipotent_antitone i ν hOrder hG hi hν) E I := by
  intro k _ _ _ _ G hG T i hi
  let := hG.isAffineHom
  let := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hOrder hInter hRoots hN hZ hU hM hUc
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  intro _ I E hE
  let D := rootSpanPointCoxeterData i ν hN hZ hG hi hRoots hν
  let := D.finiteWeyl
  let : Fintype (Weyl i) := Fintype.ofFinite _
  let : DecidableEq (Weyl i) := Classical.decEq _
  have hpos := positiveSimpleReflectionComparison_of_rootLength
    i ν hN hZ D.system hi.isSplitSubtorus.1 hRoots hν D.rootLength
  let X : JacquetComplex.CorrectedExactnessInputs.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν)
      (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν)
      hU (standardUnipotent_isUnimodular i ν hU hUc)
      (standardParabolic_monotone i ν hOrder hG hi hν)
      (standardUnipotent_antitone i ν hOrder hG hi hν) hM
      (isSemidirectDecomposition_in_levi i ν hInter hG hi hν)
      (rootAssociation i ν hN hZ) (torusPoints i) D.system :=
    { gradedVanishing := H.gradedVanishing k G hG T i hi ν hν hStandard hInter hRoots
        hN hZ hU hM D.matrix D.system D.rootLength hpos D.leviWeyl
      gradedTransition := H.gradedTransition k G hG T i hi ν hν hStandard hOrder hInter hRoots
        hN hZ hU hM hUc D.matrix D.system D.rootLength hpos D.leviWeyl
      leviWeyl := D.leviWeyl
      associationCard := fun _ _ _ hIJ _ => (rootAssociation_card_eq i ν hN hZ hIJ).symm
      associationSupport := rationalSupportCategoryAssociationInvariance.{u, v}
        k G hG T i hi ν hν hStandard hInter hRoots hN hZ hU hM
      bruhatCover := standardBruhatCover_of_rationalBruhat i ν hStandard hOrder hG hi hν hN
        (H.bruhat k G hG T i hi ν hν)
      inductionJacquet := H.inductionJacquet k G hG T i hi ν hν hStandard hInter hRoots
        hN hZ hU hM
      exactnessDetection := H.exactnessDetection k G hG T i hi ν hν hStandard hInter hRoots
        hN hZ hU hM }
  exact JacquetComplex.isExactBeforeTerminal_of_inputs.{u, u, max (u + 1) v}
    _ _ _ _ _ _ _ _ _ _ _ _ _ X E I hE

/-- The five explicit inputs imply the exact published target. This theorem
is conditional and supplies no inhabitant of its input data. -/
theorem rationalCorrectedTheorem36_of_inputs
    (H : RationalCorrectedExactnessInputs.{u, v}) :
    RationalCorrectedTheorem36Statement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  let := hG.isAffineHom
  let := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hOrder _hEndpoints hInter hRoots hN hZ hU hM hUc
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  intro _ I E hE
  exact rationalIsExactBeforeTerminal_of_inputs H k G hG T i hi ν hν hStandard hOrder hInter
    hRoots hN hZ hU hM hUc I E hE

end Langlands.Aubert.General.RationalPointFamily
