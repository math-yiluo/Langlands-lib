import Langlands.Representation.Aubert.General.RationalAlternatingOperator
import Langlands.Representation.Aubert.General.RationalLeviDecomposition
import Langlands.Representation.Aubert.General.RationalRootSignTarget
import Langlands.Representation.Aubert.GeneralCorollaryTargets
import Mathlib.NumberTheory.LocalField.Basic

/-! # Corollary 1.10 and rank-one prerequisites on actual rational points -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Group.RelativeWeylIndexing

/-- Corollary 1.10(a) for the actual standard rational-point families.
The irreducibility and actual inside-Levi cuspidality hypotheses are retained. No proof is supplied. -/
def RationalCorollary110aStatement : Prop :=
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
      (hInter : StandardLeviIntersectionStatement.{u}) (hRoots : HasRelativeRootSystem i)
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
      (hM : ∀ J, IsClosed (levi i ν J : Set (RationalPoint k G.X)))
      (hP : ∀ I, IsClosed (parabolic i ν I : Set (RationalPoint k G.X)))
      (hproj : ∀ I, Continuous
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν I).projection)
      (hUc : ∀ I, Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν I))
      (hiFl : ∀ I, PreservesFiniteLength
        (normalizedInductionFunctor.{u, max (u + 1) v}
          (isSemidirectDecomposition_of_standardCocharacterStatement
            i ν hStandard hG hi hν I) (hU I)))
      (hrFl : ∀ I, PreservesFiniteLength
        (jacquetFunctor.{u, max (u + 1) v}
          (isSemidirectDecomposition_of_standardCocharacterStatement
            i ν hStandard hG hi hν I) (hU I))),
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      letI : DecidableEq (SimpleRoot i ν) := Classical.decEq _
      corollary110a.{u, u, max (u + 1) v}
        (P := parabolic i ν) (M := levi i ν) (U := unipotent i ν)
        (h := isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν) (hU := hU)
        (hfl := standardParabolicFiniteLength
          i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl)
        (hM := hM) (hLevi := isSemidirectDecomposition_in_levi i ν hInter hG hi hν)

/-- Corollary 1.10(b) for actual reducible maximal-Levi cuspidal induction.
Both an actual length-two series and the two signed exchanges are conclusions. No proof is supplied. -/
def RationalCorollary110bStatement : Prop :=
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
      (hInter : StandardLeviIntersectionStatement.{u}) (hRoots : HasRelativeRootSystem i)
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
      (hM : ∀ J, IsClosed (levi i ν J : Set (RationalPoint k G.X)))
      (hP : ∀ I, IsClosed (parabolic i ν I : Set (RationalPoint k G.X)))
      (hproj : ∀ I, Continuous
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν I).projection)
      (hUc : ∀ I, Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν I))
      (hiFl : ∀ I, PreservesFiniteLength
        (normalizedInductionFunctor.{u, max (u + 1) v}
          (isSemidirectDecomposition_of_standardCocharacterStatement
            i ν hStandard hG hi hν I) (hU I)))
      (hrFl : ∀ I, PreservesFiniteLength
        (jacquetFunctor.{u, max (u + 1) v}
          (isSemidirectDecomposition_of_standardCocharacterStatement
            i ν hStandard hG hi hν I) (hU I))),
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      letI : DecidableEq (SimpleRoot i ν) := Classical.decEq _
      corollary110b.{u, u, max (u + 1) v}
        (P := parabolic i ν) (M := levi i ν) (U := unipotent i ν)
        (h := isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν) (hU := hU)
        (hfl := standardParabolicFiniteLength
          i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl)
        (hM := hM) (hLevi := isSemidirectDecomposition_in_levi i ν hInter hG hi hν)

/-- The length-two prerequisite at the same actual rational-point scope,
named separately from the exchange formula and its other prerequisites. No proof is supplied. -/
def RationalRankOneLengthTwoStatement : Prop :=
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
      (hInter : StandardLeviIntersectionStatement.{u}) (hRoots : HasRelativeRootSystem i)
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
      (hM : ∀ J, IsClosed (levi i ν J : Set (RationalPoint k G.X))),
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      letI : DecidableEq (SimpleRoot i ν) := Classical.decEq _
      rankOneLengthTwo.{u, u, max (u + 1) v}
        (P := parabolic i ν) (M := levi i ν) (U := unipotent i ν)
        (h := isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν) (hU := hU)
        (hM := hM) (hLevi := isSemidirectDecomposition_in_levi i ν hInter hG hi hν)

/-- Reducibility forces actual maximal-Levi self-association.
The Coxeter indexing is tied to actual roots, signs and standard Levi Weyl images. No proof is supplied. -/
def RationalRankOneSelfAssociationStatement : Prop :=
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
      (hInter : StandardLeviIntersectionStatement.{u}) (hRoots : HasRelativeRootSystem i)
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
      (hM : ∀ J, IsClosed (levi i ν J : Set (RationalPoint k G.X))),
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      letI : DecidableEq (SimpleRoot i ν) := Classical.decEq _
      ∀ [Fintype (Weyl i)]
        (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
        (C : CoxeterMatrix (SimpleRoot i ν))
        (actual : ActualCoxeterSystem (torusPoints i) C),
        RootLengthComparison i ν hN hZ actual →
        PositiveSimpleReflectionComparison i ν hN hZ actual →
        actualLeviWeylIdentification (torusPoints i) (levi i ν) actual →
        minimalityLengthCriterion actual → associatedSubsetLaws actual →
        rankOneSelfAssociation.{u, u, max (u + 1) v}
          (P := parabolic i ν) (M := levi i ν) (U := unipotent i ν)
          (h := isSemidirectDecomposition_of_standardCocharacterStatement
            i ν hStandard hG hi hν) (hU := hU)
          (hM := hM) (hLevi := isSemidirectDecomposition_in_levi i ν hInter hG hi hν)
          (T := torusPoints i) (actual := actual)

/-- The separate actual rank-one Jacquet-module prerequisite.
Every root-compatible longest lift and its literal conjugation transport are retained. No proof is supplied. -/
def RationalRankOneJacquetModulesStatement : Prop :=
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
      (hInter : StandardLeviIntersectionStatement.{u}) (hRoots : HasRelativeRootSystem i)
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
      (hM : ∀ J, IsClosed (levi i ν J : Set (RationalPoint k G.X))),
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      letI : DecidableEq (SimpleRoot i ν) := Classical.decEq _
      ∀ [Fintype (Weyl i)]
        (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
        (C : CoxeterMatrix (SimpleRoot i ν))
        (actual : ActualCoxeterSystem (torusPoints i) C),
        RootLengthComparison i ν hN hZ actual →
        PositiveSimpleReflectionComparison i ν hN hZ actual →
        actualLeviWeylIdentification (torusPoints i) (levi i ν) actual →
        minimalityLengthCriterion actual → associatedSubsetLaws actual →
        rankOneJacquetModules.{u, u, max (u + 1) v}
          (P := parabolic i ν) (M := levi i ν) (U := unipotent i ν)
          (h := isSemidirectDecomposition_of_standardCocharacterStatement
            i ν hStandard hG hi hν) (hU := hU)
          (hM := hM) (hLevi := isSemidirectDecomposition_in_levi i ν hInter hG hi hν)
          (T := torusPoints i) (actual := actual)

end Langlands.Aubert.General.RationalPointFamily
