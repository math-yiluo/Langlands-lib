import Langlands.Representation.Aubert.General.RationalIntersectionLeviConjugation
import Langlands.Representation.Aubert.General.RationalSuppliedCoxeterComparisons
import Langlands.Representation.Aubert.General.RationalGeometricSurvivors

/-! # Actual rational geometry for cuspidal Jacquet-factor extraction -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

universe u v

open Classical CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
  (ν : cocharacterLattice T) [Fintype (SimpleRoot i ν)]
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
  {C : CoxeterMatrix (SimpleRoot i ν)}
  (cs : ActualCoxeterSystem (torusPoints i) C)
  (hLength : RootLengthComparison i ν hN hZ cs)
  (hSimple : PositiveSimpleReflectionComparison i ν hN hZ cs)

include hLength hSimple in
/-- Full source and target intersections associate the original root subsets
by the very same normalizer lift of the minimum. -/
theorem rootAssociation_of_full_intersections
    (I J : Finset (SimpleRoot i ν)) (w : Weyl i) (hw : IsMinimal cs J I w)
    (n : Group.RelativeWeyl.normalizer (torusPoints i)) (hn : QuotientGroup.mk n = w)
    (hSource : intersectionSubset cs J I w = I)
    (hTarget : intersectionSubset cs I J w⁻¹ = J) :
    rootAssociation i ν hN hZ I J (n : RationalPoint k G.X) := by
  classical
  have hS : simpleImage cs w⁻¹ J ∩ I = I := by
    ext a
    simpa only [Finset.mem_inter] using
      (Finset.ext_iff.mp
        ((intersectionSubset_eq_simpleImage_inter cs hw).symm.trans hSource) a)
  have hT : simpleImage cs w I ∩ J = J := by
    ext a
    simpa only [inv_inv, Finset.mem_inter] using
      (Finset.ext_iff.mp
        ((intersectionSubset_eq_simpleImage_inter cs (isMinimal_inv cs hw)).symm.trans
          hTarget) a)
  refine ⟨n.property, ?_⟩
  change weylCharacterAction i hN hZ (QuotientGroup.mk n) '' rootSet i ν I =
    rootSet i ν J
  rw [hn]
  simpa only [hS, hT] using
    rootSet_simpleImage_intersections i ν hN hZ cs hLength hSimple I J w hw

section Topology

variable [TopologicalSpace k]

local instance rationalCuspidalExtractionPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  (hStandard : StandardCocharacterStatement.{u})
  (hInter : StandardLeviIntersectionStatement.{u})
  (hM : ∀ A, IsClosed (levi i ν A : Set (RationalPoint k G.X)))
  (hU : ∀ A, IsClosed (unipotent i ν A : Set (RationalPoint k G.X)))

/-- Structural source identities, actual decompositions, proper-source
vanishing, and actual conjugate terms when both intersections are full.
This predicate supplies no geometric filtration or proper-target exclusion. -/
def PointCuspidalExtractionGeometry : Prop :=
  PointSourceIntersectionIdentities i ν cs ∧
    GeometricIntersectionDecompositions
      (parabolic i ν) (levi i ν) (unipotent i ν) (torusPoints i) cs ∧
    PointCuspidalGeometricTermVanishing.{u, v} i ν cs hInter hG hi hν hM hU ∧
    ∀ (I J : Finset (SimpleRoot i ν)) (w : Weyl i) (_hw : IsMinimal cs J I w)
      (n : Group.RelativeWeyl.normalizer (torusPoints i)) (_hn : QuotientGroup.mk n = w)
      (hs : GeometricSourceDecomposition
        (parabolic i ν) (levi i ν) (unipotent i ν) J I n)
      (ht : GeometricTargetDecomposition
        (parabolic i ν) (levi i ν) (unipotent i ν) J I n),
      intersectionSubset cs J I w = I →
      intersectionSubset cs I J w⁻¹ = J →
      ∀ σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν I),
        ∃ hn : ∀ x : RationalPoint k G.X,
            x ∈ levi i ν J ↔
              (n : RationalPoint k G.X)⁻¹ * x * (n : RationalPoint k G.X) ∈ levi i ν I,
          rootAssociation i ν hN hZ I J (n : RationalPoint k G.X) ∧
            Nonempty
              ((geometricTermFunctor.{u, u, max (u + 1) v}
                (parabolic i ν) (levi i ν) (unipotent i ν) hM hU J I n hs ht).obj σ ≅
                (conjugationFunctor (n : RationalPoint k G.X) hn).obj σ)

include hLength hSimple hG hi hν hStandard in
/-- The full-intersection term is the actual conjugate along the same lift
that gives the root association and the dependent Levi membership witness. -/
theorem pointGeometricTerm_full_intersections
    (I J : Finset (SimpleRoot i ν)) (w : Weyl i) (hw : IsMinimal cs J I w)
    (n : Group.RelativeWeyl.normalizer (torusPoints i)) (hn : QuotientGroup.mk n = w)
    (hs : GeometricSourceDecomposition
      (parabolic i ν) (levi i ν) (unipotent i ν) J I n)
    (ht : GeometricTargetDecomposition
      (parabolic i ν) (levi i ν) (unipotent i ν) J I n)
    (hSource : intersectionSubset cs J I w = I)
    (hTarget : intersectionSubset cs I J w⁻¹ = J)
    (σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν I)) :
    ∃ hn : ∀ x : RationalPoint k G.X,
        x ∈ levi i ν J ↔
          (n : RationalPoint k G.X)⁻¹ * x * (n : RationalPoint k G.X) ∈ levi i ν I,
      rootAssociation i ν hN hZ I J (n : RationalPoint k G.X) ∧
        Nonempty
          ((geometricTermFunctor.{u, u, max (u + 1) v}
            (parabolic i ν) (levi i ν) (unipotent i ν) hM hU J I n hs ht).obj σ ≅
            (conjugationFunctor (n : RationalPoint k G.X) hn).obj σ) := by
  have hA := rootAssociation_of_full_intersections
    i ν hN hZ cs hLength hSimple I J w hw n hn hSource hTarget
  let hConj := conjugationMembership_of_rootAssociation
    i ν hG hi hν hStandard hN hZ I J n hA
  exact ⟨hConj, hA, ⟨geometricTermFullLeviIso.{u, u, max (u + 1) v}
    (parabolic i ν) (levi i ν) (unipotent i ν) hM hU J I n hs ht hConj σ⟩⟩

include hLength hSimple hStandard in
/-- Root comparisons and the displayed standard data prove the geometric
inputs used for extraction, with no representation finiteness premise. -/
theorem pointCuspidalExtractionGeometry_of_rootComparisons :
    PointCuspidalExtractionGeometry.{u, v} i ν hN hZ cs hG hi hν hInter hM hU := by
  have hSource := pointSourceIntersectionIdentities
    i ν hN hZ cs hStandard hG hi hν hInter hLength hSimple
  refine ⟨hSource, geometricIntersectionDecompositions_of_pointSource
    i ν cs hSource hInter hG hi hν, ?_, ?_⟩
  · exact pointCuspidalGeometricTermVanishing_of_rootComparisons
      i ν hN hZ cs hLength hSimple hStandard hInter hG hi hν hM hU
  · intro I J w hw n hn hs ht hS hT σ
    exact pointGeometricTerm_full_intersections
      i ν hN hZ cs hLength hSimple hG hi hν hStandard hM hU
      I J w hw n hn hs ht hS hT σ

include hStandard in
/-- The existing actual relative-root-system witness constructs one point
Coxeter system with all these geometric inputs. Root comparisons are derived,
rather than added to the rational extraction target. -/
theorem rootSpanPointCoxeterData_cuspidalExtractionGeometry
    (hRoots : HasRelativeRootSystem i) :
    PointCuspidalExtractionGeometry.{u, v} i ν hN hZ
      (rootSpanPointCoxeterData i ν hN hZ hG hi hRoots hν).system
      hG hi hν hInter hM hU := by
  let d := rootSpanPointCoxeterData i ν hN hZ hG hi hRoots hν
  exact pointCuspidalExtractionGeometry_of_rootComparisons
    i ν hN hZ d.system d.rootLength
    (positiveSimpleReflectionComparison_of_rootLength
      i ν hN hZ d.system hi.isSplitSubtorus.1 hRoots hν d.rootLength)
    hG hi hν hStandard hInter hM hU

end Topology

end Langlands.Aubert.General.RationalPointFamily
