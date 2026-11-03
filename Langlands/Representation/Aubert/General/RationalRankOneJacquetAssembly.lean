import Langlands.Representation.Aubert.General.RankOneJacquetSupportDeduction
import Langlands.Representation.Aubert.General.RationalSupportCategoryTargets
import Langlands.Representation.Aubert.General.RationalUnipotentRegularity
import Langlands.Representation.Aubert.General.RootAssociationLaws

/-! # Actual rational-point rank-one assembly from support detection -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep
open Langlands.AlgebraicGeometry.PointTopology

/-- Specialize the support-detection assembly to the actual rational-point
families. Identity association and properness of associates are derived from
the actual root action; the detector and local exact data remain supplied. -/
def rankOneJacquetConstituentsOfRationalSupportDetection
    (hdet : RationalSupportCategoryIrreducibleJacquetDetectionStatement.{u, v}) :
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
        (_hN : HasPointNormalizerComparison i) (_hZ : HasPointCentralizerComparison i)
        (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
        (hM : ∀ I, IsClosed (levi i ν I : Set (RationalPoint k G.X))),
        letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
        let h := isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν
        let hL := isSemidirectDecomposition_in_levi i ν hInter hG hi hν
        ∀ (J : Finset (SimpleRoot i ν)) (_hJ : J ≠ Finset.univ)
          (σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν J))
          (_hσ : σ.IsIrreducible)
          (_hc : IsCorollaryLeviCuspidal.{u, u, max (u + 1) v}
            (parabolic i ν) (levi i ν) (unipotent i ν) J (hM J) (hL J) hU σ)
          (n : Langlands.Group.RelativeWeyl.normalizer (torusPoints i))
          (hself : ∀ x : RationalPoint k G.X,
            x ∈ levi i ν J ↔ (n : RationalPoint k G.X) * x * (n : RationalPoint k G.X)⁻¹
              ∈ levi i ν J)
          (A B : FiniteLengthObject.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X))
          (_hseries : HasTwoConstituents
            ((normalizedInductionFunctor (h J) (hU J)).obj σ) A.val B.val)
          (_hgeometry : HasRankOneJacquetMiddleSequence.{u, u, max (u + 1) v}
            (h := h) (hU := hU) J σ n hself)
          (_hvanish : ∀ K : Finset (SimpleRoot i ν), K ≠ Finset.univ → K ≠ J →
            IsZero ((jacquetFunctor (h K) (hU K)).obj
              ((normalizedInductionFunctor (h J) (hU J)).obj σ))),
          {ρ : FiniteLengthObject.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X) ×
              FiniteLengthObject.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X) //
            HasTwoConstituents ((normalizedInductionFunctor (h J) (hU J)).obj σ)
              ρ.1.val ρ.2.val ∧
            RankOneJacquetPattern.{u, u, max (u + 1) v}
              (parabolic i ν) (levi i ν) (unipotent i ν)
              h hU (torusPoints i) J σ ρ.1.val ρ.2.val n hself} := by
  intro k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hInter hRoots hN hZ hU hM
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  dsimp only
  intro J hJ σ hσ hc n hself A B hseries hgeometry hvanish
  exact rankOneJacquetConstituentsOfSupportDetection.{u, u, max (u + 1) v}
    (P := parabolic i ν) (M := levi i ν) (U := unipotent i ν)
    (h := isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν) (hU := hU) (hM := hM)
    (hL := isSemidirectDecomposition_in_levi i ν hInter hG hi hν)
    (IsAssociate := rootAssociation i ν hN hZ)
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν hStandard hG hi hν)
    (hdet k G hG T i hi ν hν hStandard hInter hRoots hN hZ hU hM)
    J (rootAssociation_one i ν hN hZ J)
    (fun _ _ hJK => rootAssociation_ne_univ i ν hN hZ hJK hJ)
    σ hσ
    ((isCorollaryLeviCuspidal_iff_isLeviCuspidal.{u, u, max (u + 1) v}
      (P := parabolic i ν) (M := levi i ν) (U := unipotent i ν) (hU := hU)
      J (hM J) (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J) σ).mp hc)
    n hself A B hseries hgeometry hvanish

end Langlands.Aubert.General.RationalPointFamily
