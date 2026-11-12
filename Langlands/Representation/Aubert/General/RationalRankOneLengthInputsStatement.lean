import Langlands.Representation.Aubert.General.RationalCorollaryTargets
import Langlands.Representation.Aubert.General.RationalCuspidalJacquetFactorTarget
import Langlands.Representation.Filtration.RepresentationLength

/-! # Detection and Jacquet-length inputs for rational rank-one length two -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep
open Langlands.AlgebraicGeometry.PointTopology

/-- Every actual irreducible subquotient of the actual normalized induction of an
irreducible inside-Levi cuspidal representation of a maximal standard Levi has a
nonzero actual normalized Jacquet module along some maximal proper standard
parabolic `univ.erase β`. Reducibility of the induction is not assumed.
No proof is supplied. -/
def RationalMaximalCuspidalJacquetDetectionStatement : Prop :=
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
      ∀ (J : Finset (SimpleRoot i ν)), IsMaximalStandard J →
      ∀ σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν J),
        σ.IsIrreducible →
        IsCorollaryLeviCuspidal.{u, u, max (u + 1) v} (parabolic i ν) (levi i ν)
          (unipotent i ν) J (hM J)
          (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J) hU σ →
        ∀ D : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X),
          D.IsIrreducible →
          SmoothRep.IsSubquotient D
            ((normalizedInductionFunctor.{u, max (u + 1) v}
              (isSemidirectDecomposition_of_standardCocharacterStatement
                i ν hStandard hG hi hν J) (hU J)).obj σ) →
          ∃ β : SimpleRoot i ν,
            Nontrivial ((jacquetFunctor.{u, max (u + 1) v}
              (isSemidirectDecomposition_of_standardCocharacterStatement
                i ν hStandard hG hi hν (Finset.univ.erase β))
              (hU (Finset.univ.erase β))).obj D)

/-- For the same data, the actual composition lengths of the normalized Jacquet
modules of that induction along all maximal proper standard parabolics
`univ.erase β` add up to at most two, in `ℕ∞`. No proof is supplied. -/
def RationalMaximalCuspidalJacquetBudgetStatement : Prop :=
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
      ∀ (J : Finset (SimpleRoot i ν)), IsMaximalStandard J →
      ∀ σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν J),
        σ.IsIrreducible →
        IsCorollaryLeviCuspidal.{u, u, max (u + 1) v} (parabolic i ν) (levi i ν)
          (unipotent i ν) J (hM J)
          (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J) hU σ →
        (∑ β : SimpleRoot i ν,
          repLength ((jacquetFunctor.{u, max (u + 1) v}
            (isSemidirectDecomposition_of_standardCocharacterStatement
              i ν hStandard hG hi hν (Finset.univ.erase β))
            (hU (Finset.univ.erase β))).obj
            ((normalizedInductionFunctor.{u, max (u + 1) v}
              (isSemidirectDecomposition_of_standardCocharacterStatement
                i ν hStandard hG hi hν J) (hU J)).obj σ)).representation) ≤ 2

/-- The detection and Jacquet-length inputs together imply the rational
rank-one length-two target. No proof is supplied here. -/
def RationalRankOneLengthTwoFromInputsStatement : Prop :=
  RationalMaximalCuspidalJacquetDetectionStatement.{u, v} →
    RationalMaximalCuspidalJacquetBudgetStatement.{u, v} →
    RationalRankOneLengthTwoStatement.{u, v}

/-- The actual cuspidal Jacquet-factor extraction proposition implies the
detection input. No proof is supplied here. -/
def RationalMaximalCuspidalJacquetDetectionFromExtractionStatement : Prop :=
  RationalCuspidalJacquetFactorExtractionStatement.{u, v} →
    RationalMaximalCuspidalJacquetDetectionStatement.{u, v}

end Langlands.Aubert.General.RationalPointFamily
