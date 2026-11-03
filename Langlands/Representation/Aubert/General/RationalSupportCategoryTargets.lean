import Langlands.Representation.Aubert.General.RationalStandardComplex
import Langlands.Representation.Aubert.General.RationalLeviDecomposition
import Langlands.Representation.Aubert.General.SupportCategoryStatements
import Mathlib.NumberTheory.LocalField.Basic

/-! # Support-theory targets on the actual rational-point smooth category -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

/-- Renard, Corollaire VI.2.1, on the actual standard rational-point families:
every irreducible smooth representation lies in some actual cuspidal series.
No proof is supplied. -/
def RationalCuspidalSeriesExistenceStatement : Prop :=
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
      (hInter : StandardLeviIntersectionStatement.{u})
      (hRoots : HasRelativeRootSystem i)
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
      (hM : ∀ I, IsClosed (levi i ν I : Set (RationalPoint k G.X))),
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      CuspidalSeriesExistenceTarget.{u, u, max (u + 1) v}
        (P := parabolic i ν) (M := levi i ν) (U := unipotent i ν)
        (h := isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν)
        (hU := hU) (hM := hM)
        (hL := isSemidirectDecomposition_in_levi i ν hInter hG hi hν)

/-- Renard, Théorème VI.5.4, on the actual families: two actual cuspidal data
of one irreducible representation are associated by an actual normalizer
representative carrying the simple-root subsets and conjugating the Levis.
No proof is supplied. -/
def RationalCuspidalSupportAssociationStatement : Prop :=
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
      (hInter : StandardLeviIntersectionStatement.{u})
      (hRoots : HasRelativeRootSystem i)
      (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
      (hM : ∀ I, IsClosed (levi i ν I : Set (RationalPoint k G.X))),
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      CuspidalSupportAssociationTarget.{u, u, max (u + 1) v}
        (P := parabolic i ν) (M := levi i ν) (U := unipotent i ν)
        (h := isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν)
        (hU := hU) (hM := hM)
        (hL := isSemidirectDecomposition_in_levi i ν hInter hG hi hν)
        (IsAssociate := rootAssociation i ν hN hZ)

/-- Erratum, p. 4687, on the actual families: the actual support category
depends only on the association class of the standard Levi. No proof is
supplied. -/
def RationalSupportCategoryAssociationInvarianceStatement : Prop :=
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
      (hInter : StandardLeviIntersectionStatement.{u})
      (hRoots : HasRelativeRootSystem i)
      (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
      (hM : ∀ I, IsClosed (levi i ν I : Set (RationalPoint k G.X))),
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      SupportCategoryAssociationInvarianceTarget.{u, u, max (u + 1) v}
        (P := parabolic i ν) (M := levi i ν) (U := unipotent i ν)
        (h := isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν)
        (hU := hU) (hM := hM)
        (hL := isSemidirectDecomposition_in_levi i ν hInter hG hi hν)
        (IsAssociate := rootAssociation i ν hN hZ)

/-- Proof of Renard, Théorème VI.5.4, on the actual families: an irreducible
member of the actual support category has a nonzero actual normalized Jacquet
module along some associated standard Levi. No proof is supplied. -/
def RationalSupportCategoryIrreducibleJacquetDetectionStatement : Prop :=
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
      (hInter : StandardLeviIntersectionStatement.{u})
      (hRoots : HasRelativeRootSystem i)
      (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
      (hM : ∀ I, IsClosed (levi i ν I : Set (RationalPoint k G.X))),
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      SupportCategoryIrreducibleJacquetDetectionTarget.{u, u, max (u + 1) v}
        (P := parabolic i ν) (M := levi i ν) (U := unipotent i ν)
        (h := isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν)
        (hU := hU) (hM := hM)
        (hL := isSemidirectDecomposition_in_levi i ν hInter hG hi hν)
        (IsAssociate := rootAssociation i ν hN hZ)

/-- Erratum, p. 4687, on the actual families: a member of the actual support
category whose actual normalized Jacquet modules along all associated standard
Levis vanish is zero. No proof is supplied. -/
def RationalSupportCategoryZeroDetectionStatement : Prop :=
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
      (hInter : StandardLeviIntersectionStatement.{u})
      (hRoots : HasRelativeRootSystem i)
      (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
      (hM : ∀ I, IsClosed (levi i ν I : Set (RationalPoint k G.X))),
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      SupportCategoryZeroDetectionTarget.{u, u, max (u + 1) v}
        (P := parabolic i ν) (M := levi i ν) (U := unipotent i ν)
        (h := isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν)
        (hU := hU) (hM := hM)
        (hL := isSemidirectDecomposition_in_levi i ν hInter hG hi hν)
        (IsAssociate := rootAssociation i ν hN hZ)

/-- Erratum, p. 4687, on the actual families: exactness at a member of the
actual support category is detected by the actual normalized Jacquet modules
along all associated standard Levis. No proof is supplied. -/
def RationalSupportCategoryExactnessDetectionStatement : Prop :=
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
      (hInter : StandardLeviIntersectionStatement.{u})
      (hRoots : HasRelativeRootSystem i)
      (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
      (hM : ∀ I, IsClosed (levi i ν I : Set (RationalPoint k G.X))),
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      SupportCategoryExactnessDetectionTarget.{u, u, max (u + 1) v}
        (P := parabolic i ν) (M := levi i ν) (U := unipotent i ν)
        (h := isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν)
        (hU := hU) (hM := hM)
        (hL := isSemidirectDecomposition_in_levi i ν hInter hG hi hν)
        (IsAssociate := rootAssociation i ν hN hZ)

/-- Renard, Théorème VI.7.2 and Proposition VI.7.3, on the actual families: the
actual support category is stable under actual normalized induction after
actual normalized Jacquet restriction along every standard Levi. No proof is
supplied. -/
def RationalSupportCategoryInductionJacquetStatement : Prop :=
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
      (hInter : StandardLeviIntersectionStatement.{u})
      (hRoots : HasRelativeRootSystem i)
      (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
      (hM : ∀ I, IsClosed (levi i ν I : Set (RationalPoint k G.X))),
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      SupportCategoryInductionJacquetTarget.{u, u, max (u + 1) v}
        (P := parabolic i ν) (M := levi i ν) (U := unipotent i ν)
        (h := isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν)
        (hU := hU) (hM := hM)
        (hL := isSemidirectDecomposition_in_levi i ν hInter hG hi hν)
        (IsAssociate := rootAssociation i ν hN hZ)

/-- Renard, Propositions VI.5.3 (i) and VI.7.3, on the actual families: if no
standard Levi inside `L_K` is associated to `L_I`, the actual normalized
Jacquet module along `L_K` of every member of the actual support category is
zero. No proof is supplied. -/
def RationalSupportCategoryJacquetVanishingStatement : Prop :=
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
      (hInter : StandardLeviIntersectionStatement.{u})
      (hRoots : HasRelativeRootSystem i)
      (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
      (hM : ∀ I, IsClosed (levi i ν I : Set (RationalPoint k G.X))),
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      SupportCategoryJacquetVanishingTarget.{u, u, max (u + 1) v}
        (P := parabolic i ν) (M := levi i ν) (U := unipotent i ν)
        (h := isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν)
        (hU := hU) (hM := hM)
        (hL := isSemidirectDecomposition_in_levi i ν hInter hG hi hν)
        (IsAssociate := rootAssociation i ν hN hZ)

/-- Renard, Théorème VI.7.2, on the actual families: every smooth
representation is an internal direct sum of subrepresentations lying in the
actual support categories. No proof is supplied. -/
def RationalSupportCategoryDecompositionStatement : Prop :=
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
      (hInter : StandardLeviIntersectionStatement.{u})
      (hRoots : HasRelativeRootSystem i)
      (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
      (hM : ∀ I, IsClosed (levi i ν I : Set (RationalPoint k G.X))),
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      SupportCategoryDecompositionTarget.{u, u, max (u + 1) v}
        (P := parabolic i ν) (M := levi i ν) (U := unipotent i ν)
        (h := isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν)
        (hU := hU) (hM := hM)
        (hL := isSemidirectDecomposition_in_levi i ν hInter hG hi hν)
        (IsAssociate := rootAssociation i ν hN hZ)

end Langlands.Aubert.General.RationalPointFamily
