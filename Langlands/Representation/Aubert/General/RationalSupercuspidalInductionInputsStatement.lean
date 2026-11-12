import Langlands.Representation.Aubert.General.RationalSupercuspidalInductionFiniteLengthStatement
import Langlands.Representation.Aubert.General.RationalSupportCategoryTargets

/-! # Jacquet-length input for actual supercuspidal induction -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

/-- A consequence of Renard, Proposition VI.5.3 (iii), on the actual standard
rational-point families: if a normalizer point carries the simple-root subset
`I` onto `J`, then the actual normalized Jacquet module along `J` of the actual
normalized induction of an irreducible inside-Levi cuspidal representation of
`levi i ν I` has finite length. No proof is supplied. -/
def RationalAssociatedCuspidalJacquetFiniteLengthStatement : Prop :=
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
      let h := isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν
      let hL := isSemidirectDecomposition_in_levi i ν hInter hG hi hν
      ∀ (I J : Finset (SimpleRoot i ν)) (n : RationalPoint k G.X),
        rootAssociation i ν hN hZ I J n →
        ∀ σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν I),
          σ.IsIrreducible →
          IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν)
            hU I (hM I) (hL I) σ →
          ((jacquetFunctor.{u, max (u + 1) v} (h J) (hU J)).obj
            ((normalizedInductionFunctor.{u, max (u + 1) v} (h I) (hU I)).obj σ)).HasFiniteLength

/-- Irreducible Jacquet detection along associated standard Levis and the
associated Jacquet finite-length input together imply the finite-length part of
Renard, Théorème VI.5.4, on the actual standard families. The two inputs are
taken at the carrier parameter `v` of the target's input universe. No proof is
supplied here. -/
def RationalSupercuspidalInductionFiniteLengthFromInputsStatement : Prop :=
  RationalSupportCategoryIrreducibleJacquetDetectionStatement.{u, v} →
    RationalAssociatedCuspidalJacquetFiniteLengthStatement.{u, v} →
    RationalSupercuspidalInductionFiniteLengthStatement.{u, v}

end Langlands.Aubert.General.RationalPointFamily
