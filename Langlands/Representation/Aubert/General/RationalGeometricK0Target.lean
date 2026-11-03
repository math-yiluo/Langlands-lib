import Langlands.Representation.Aubert.General.RationalAlternatingOperator
import Langlands.Representation.Aubert.General.RationalRootSignTarget
import Langlands.Representation.Aubert.General.GeometricK0Target
import Mathlib.NumberTheory.LocalField.Basic

/-! # Geometric-lemma K0 expansion on the actual rational-point family -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

/-- Aubert (1.3) on the literal standard rational-point families.
Actual intersection decompositions and representation preservation are
separate inputs; no expansion is supplied by either one. -/
def RationalGeometricK0ExpansionStatement : Prop :=
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
      (hStandard : StandardCocharacterStatement.{u}) (hRoots : HasRelativeRootSystem i)
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
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
            i ν hStandard hG hi hν I) (hU I)))
      (hM : ∀ I, IsClosed (levi i ν I : Set (RationalPoint k G.X))),
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      ∀ [Fintype (Weyl i)]
        (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
        (CM : CoxeterMatrix (SimpleRoot i ν))
        (cs : ActualCoxeterSystem (torusPoints i) CM),
        RootLengthComparison i ν hN hZ cs →
        PositiveSimpleReflectionComparison i ν hN hZ cs →
        actualLeviWeylIdentification (torusPoints i) (levi i ν) cs →
        ∀ (hGeom : GeometricIntersectionDecompositions
          (parabolic i ν) (levi i ν) (unipotent i ν) (torusPoints i) cs)
          (hTermFl : ∀ (I J : Finset (SimpleRoot i ν)) (w : Weyl i)
            (hw : IsMinimal cs I J w)
            (n : Group.RelativeWeyl.normalizer (torusPoints i))
            (hn : QuotientGroup.mk n = w),
            GeometricTermFiniteLength.{u, u, max (u + 1) v}
              (parabolic i ν) (levi i ν) (unipotent i ν) hM hU I J
              (n : RationalPoint k G.X)
              (hGeom I J w hw n hn).1 (hGeom I J w hw n hn).2),
          GeometricK0ExpansionStatement.{u, u, max (u + 1) v}
            (parabolic i ν) (levi i ν) (unipotent i ν)
            (isSemidirectDecomposition_of_standardCocharacterStatement
              i ν hStandard hG hi hν) hU
            (standardParabolicFiniteLength.{u, v}
              i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl)
            hM (torusPoints i) cs hGeom hTermFl

end Langlands.Aubert.General.RationalPointFamily
