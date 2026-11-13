import Langlands.Group.RelativeWeylFullIntersectionCounts
import Langlands.Representation.Aubert.General.RationalCoatomGeometricBudget
import Langlands.Representation.Aubert.General.RationalInducedJacquetGeometricFiltration

/-! # Exact lengths of equal-rank actual induced Jacquet modules -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open Classical GroupScheme SmoothRep Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] (ν : cocharacterLattice T)

local instance rationalAssociatedJacquetBudgetPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
  [Fintype (SimpleRoot i ν)] [Fintype (Weyl i)]
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
  {C : CoxeterMatrix (SimpleRoot i ν)}
  (cs : ActualCoxeterSystem (torusPoints i) C)
  (hIdent : actualLeviWeylIdentification (torusPoints i) (levi i ν) cs)
  (hLength : RootLengthComparison i ν hN hZ cs)
  (hStandard : StandardCocharacterStatement.{u})
  (hInter : StandardLeviIntersectionStatement.{u})
  (hRoots : HasRelativeRootSystem i)
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  (hM : ∀ A, IsClosed (levi i ν A : Set (RationalPoint k G.X)))
  (hU : ∀ A, IsClosed (unipotent i ν A : Set (RationalPoint k G.X)))

/-- The actual ordered induced Jacquet filtration with its bijective minimal
class enumeration, using the proved Haar correction cancellation. -/
def pointInducedJacquetObjectFiltration
    (I J : Finset (SimpleRoot i ν))
    (σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν I)) :
    PointGeometricObjectFiltration.{u, v}
      i ν hG hi hν hStandard hM hU cs J I σ := by
  have hSimple := positiveSimpleReflectionComparison_of_rootLength
    i ν hN hZ cs hi.isSplitSubtorus.1 hRoots hν hLength
  let hP := isClosed_standard_parabolic i ν hStandard hG hi hν
  let hproj := continuous_standard_projection i ν hStandard hG hi hν
  exact pointGeometricObjectFiltrationOfEpsilonBalance.{u, v}
    i ν hG hi hν hStandard hN hZ cs hIdent hM hU hInter hLength hSimple J I
    (fun _ _ n _ => geometricEpsilon_mul_eq_one
      i ν hStandard hG hi hν hN hRoots J I _ _ n hU hP hM (hproj J) (hproj I)) σ

include hLength in
/-- A supplied actual geometric object filtration computes the equal-rank
Jacquet length by its bijective minimal-representative enumeration. -/
theorem pointInducedJacquet_repLength_eq_fullIntersectionCount_of_filtration
    (hSimple : PositiveSimpleReflectionComparison i ν hN hZ cs)
    (I J : Finset (SimpleRoot i ν)) (hcard : I.card = J.card)
    (σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν I))
    (hσ : σ.IsIrreducible)
    (hc : IsCorollaryLeviCuspidal.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν) I (hM I)
      (isSemidirectDecomposition_in_levi i ν hInter hG hi hν I) hU σ)
    (D : PointGeometricObjectFiltration.{u, v}
      i ν hG hi hν hStandard hM hU cs J I σ) :
    repLength (pointInducedJacquetObject i ν hG hi hν hStandard hU J I σ).representation =
      ((fullIntersectionRepresentatives cs J I).card : ℕ∞) := by
  classical
  calc
    _ = ∑ q, repLength (D.filtration.gradedRepresentation q).ρ :=
      repLength_eq_sum_of_filtration D.filtration
    _ = ∑ q, if intersectionSubset cs J I (D.enumeration q).val = I
        then (1 : ℕ∞) else 0 := by
      apply Finset.sum_congr rfl
      intro q _
      rw [repLength_congr (Representation.equivOfIso (D.grade q))]
      exact pointGeometricTerm_repLength.{u, v}
        i ν hN hZ cs hLength hSimple hG hi hν hStandard hInter hM hU
        J I (D.enumeration q).val
        ((mem_minimalReps cs J I _).mp (D.enumeration q).property)
        (D.lift q) (D.lift_class q) (D.source q) (D.target q) hcard σ hσ hc
    _ = _ := by
      convert (sum_fullIntersectionIndicators (R := ℕ∞) cs J I D.enumeration) using 1
      apply Finset.sum_congr rfl
      intro q _
      split_ifs <;> rfl

include hN hZ hIdent hLength hRoots in
/-- For equal-rank source and target, the actual induced Jacquet length is
the number of minimal Weyl representatives with full source intersection. -/
theorem pointInducedJacquet_repLength_eq_fullIntersectionCount
    (I J : Finset (SimpleRoot i ν)) (hcard : I.card = J.card)
    (σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν I))
    (hσ : σ.IsIrreducible)
    (hc : IsCorollaryLeviCuspidal.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν) I (hM I)
      (isSemidirectDecomposition_in_levi i ν hInter hG hi hν I) hU σ) :
    repLength (pointInducedJacquetObject i ν hG hi hν hStandard hU J I σ).representation =
      ((fullIntersectionRepresentatives cs J I).card : ℕ∞) := by
  have hSimple := positiveSimpleReflectionComparison_of_rootLength
    i ν hN hZ cs hi.isSplitSubtorus.1 hRoots hν hLength
  exact pointInducedJacquet_repLength_eq_fullIntersectionCount_of_filtration.{u, v}
    i ν hN hZ cs hLength hStandard hInter hG hi hν hM hU hSimple I J hcard σ hσ hc
    (pointInducedJacquetObjectFiltration.{u, v}
      i ν hN hZ cs hIdent hLength hStandard hInter hRoots hG hi hν hM hU I J σ)

end Langlands.Aubert.General.RationalPointFamily
