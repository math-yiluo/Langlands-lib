import Langlands.Representation.Aubert.General.RationalPointSourceGeometry
import Langlands.Representation.Aubert.General.RationalSourceJacquet
import Langlands.Representation.Aubert.General.RankOneJacquetAssembly

/-! # Vanishing of actual geometric terms on rational cuspidal data -/

noncomputable section

universe uI uG uV u v

open Classical
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General

open SmoothRep Group.RelativeWeylIndexing

section Generic

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {Index : Type uI} (P M U : Finset Index → Subgroup G)
  (hM : ∀ I, IsClosed (M I : Set G)) (hU : ∀ I, IsClosed (U I : Set G))
  (J : Finset Index)
  (hJ : ∀ K : Finset J, IsSemidirectDecomposition
    ((P (leviIndex J K)).subgroupOf (M J))
    ((M (leviIndex J K)).subgroupOf (M J))
    ((U (leviIndex J K)).subgroupOf (M J)))
  (σ : SmoothRep.{0, uG, uV} ℂ (M J))
  (hc : IsLeviCuspidal P M U hU J (hM J) hJ σ)

include hJ hc in
/-- Cuspidality kills the actual source Jacquet module when its Levi and
radical are those of a proper restricted standard parabolic. -/
theorem geometricSourceJacquet_subsingleton_of_cuspidal
    (I : Finset Index) (K : Finset J) (hK : K ≠ Finset.univ) (n : G)
    (hs : GeometricSourceDecomposition P M U I J n)
    (hLevi : geometricSourceIntersection (M I) (M J) n = M (leviIndex J K))
    (hRadical : (geometricSourceIntersection (U I) (M J) n).subgroupOf (M J) =
      (U (leviIndex J K)).subgroupOf (M J)) :
    Subsingleton ((geometricSourceJacquetFunctor.{uI, uG, uV}
      P M U hM hU I J n hs).obj σ) := by
  let _ := (hM J).locallyCompactSpace
  have hKJ : M (leviIndex J K) ≤ M J := by
    rw [← hLevi]
    exact inf_le_left
  let e := (geometricSourceJacquetComparisonIso.{uI, uG, uV}
    P M U hM hU I J (leviIndex J K) n hs hKJ (hJ K) hLevi hRadical).app σ
  exact ⟨fun a b => (SmoothRep.equivOfIso e).injective ((hc ⟨K, hK⟩).elim _ _)⟩

private theorem induction_subsingleton {P' M' U' : Subgroup G}
    (h : IsSemidirectDecomposition P' M' U') (hU' : IsClosed (U' : Set G))
    (A : SmoothRep.{0, uG, uV} ℂ M') (hz : Subsingleton A) :
    Subsingleton ((normalizedInductionFunctor h hU').obj A) := by
  let _ := hz
  change Subsingleton (Induction.SmoothFunctions P' (inducingRepresentation h hU' A))
  infer_instance

/-- The entire actual geometric term vanishes after its source Jacquet
module vanishes. No finite-length preservation is required. -/
theorem geometricTerm_subsingleton_of_source_subsingleton
    (I : Finset Index) (n : G)
    (hs : GeometricSourceDecomposition P M U I J n)
    (ht : GeometricTargetDecomposition P M U I J n)
    (A : SmoothRep.{0, uG, max uG uV} ℂ (M J))
    (hz : Subsingleton ((geometricSourceJacquetFunctor.{uI, uG, max uG uV}
      P M U hM hU I J n hs).obj A)) :
    Subsingleton ((geometricTermFunctor.{uI, uG, uV}
      P M U hM hU I J n hs ht).obj A) := by
  let _ := (hM I).locallyCompactSpace
  refine induction_subsingleton _ _ _ ?_
  change Subsingleton ((geometricSourceJacquetFunctor.{uI, uG, max uG uV}
    P M U hM hU I J n hs).obj A)
  exact hz

end Generic

namespace RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [TopologicalSpace k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
  (ν : cocharacterLattice T) [Fintype (SimpleRoot i ν)]
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
  {C : CoxeterMatrix (SimpleRoot i ν)}
  (actual : ActualCoxeterSystem (torusPoints i) C)
  (hLength : RootLengthComparison i ν hN hZ actual)
  (hSimple : PositiveSimpleReflectionComparison i ν hN hZ actual)
  (hStandard : StandardCocharacterStatement.{u})
  (hInter : StandardLeviIntersectionStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)

local instance rationalCuspidalGeometricPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  (hM : ∀ A, IsClosed (levi i ν A : Set (RationalPoint k G.X)))
  (hU : ∀ A, IsClosed (unipotent i ν A : Set (RationalPoint k G.X)))

/-- Actual geometric terms on cuspidal data vanish whenever their source
intersection is proper. The original categorical cuspidality is retained. -/
def PointCuspidalGeometricTermVanishing : Prop :=
  ∀ (I J : Finset (SimpleRoot i ν)) (w : Weyl i), IsMinimal actual I J w →
    ∀ (n : Group.RelativeWeyl.normalizer (torusPoints i)), QuotientGroup.mk n = w →
      ∀ (hs : GeometricSourceDecomposition
          (parabolic i ν) (levi i ν) (unipotent i ν) I J n)
        (ht : GeometricTargetDecomposition
          (parabolic i ν) (levi i ν) (unipotent i ν) I J n)
        (σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν J)),
        IsCorollaryLeviCuspidal.{u, u, max (u + 1) v} (parabolic i ν) (levi i ν) (unipotent i ν)
          J (hM J) (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J) hU σ →
        intersectionSubset actual I J w ≠ J →
        Subsingleton ((geometricTermFunctor.{u, u, max (u + 1) v}
          (parabolic i ν) (levi i ν) (unipotent i ν) hM hU I J n hs ht).obj σ)

include hLength hSimple hStandard in
/-- A proper intrinsic source intersection makes the actual source Jacquet
module zero, using only the original root and standard-cocharacter inputs. -/
theorem pointGeometricSourceJacquet_subsingleton_of_cuspidal
    (I J : Finset (SimpleRoot i ν)) (w : Weyl i) (hw : IsMinimal actual I J w)
    (n : Group.RelativeWeyl.normalizer (torusPoints i)) (hn : QuotientGroup.mk n = w)
    (hs : GeometricSourceDecomposition
      (parabolic i ν) (levi i ν) (unipotent i ν) I J n)
    (σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν J))
    (hc : IsCorollaryLeviCuspidal.{u, u, max (u + 1) v} (parabolic i ν) (levi i ν) (unipotent i ν)
      J (hM J) (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J) hU σ)
    (hproper : intersectionSubset actual I J w ≠ J) :
    Subsingleton ((geometricSourceJacquetFunctor.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν) hM hU I J n hs).obj σ) := by
  classical
  let K := intersectionLeviIndex actual I J w
  have hlabels : leviIndex J K = simpleImage actual w⁻¹ I ∩ J := by
    calc
      leviIndex J K = intersectionSubset actual I J w :=
        leviIndex_intersectionLeviIndex actual I J w
      _ = simpleImage actual w⁻¹ I ∩ J := by
        ext a
        simpa only [Finset.mem_inter] using
          (Finset.ext_iff.mp (intersectionSubset_eq_simpleImage_inter actual hw) a)
  have hK : K ≠ Finset.univ := by
    intro hfull
    apply hproper
    calc
      intersectionSubset actual I J w = leviIndex J K :=
        (leviIndex_intersectionLeviIndex actual I J w).symm
      _ = J := by
        rw [hfull]
        ext a
        simp [leviIndex]
  obtain ⟨hL, -, hRad⟩ := pointSourceIntersectionIdentities
    i ν hN hZ actual hStandard hG hi hν hInter hLength hSimple I J w hw n hn
  rw [← hlabels] at hL hRad
  exact geometricSourceJacquet_subsingleton_of_cuspidal
    (parabolic i ν) (levi i ν) (unipotent i ν) hM hU J
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J) σ
    ((isCorollaryLeviCuspidal_iff_isLeviCuspidal.{u, u, max (u + 1) v} J (hM J)
      (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J) σ).mp hc)
    I K hK n hs hL hRad

include hLength hSimple hStandard in
/-- Root comparisons and the original cuspidality prove proper-source
vanishing for every actual lift and every actual decomposition witness. -/
theorem pointCuspidalGeometricTermVanishing_of_rootComparisons :
    PointCuspidalGeometricTermVanishing.{u, v}
      i ν actual hInter hG hi hν hM hU := by
  intro I J w hw n hn hs ht σ hc hproper
  exact geometricTerm_subsingleton_of_source_subsingleton.{u, u, max (u + 1) v}
    (parabolic i ν) (levi i ν) (unipotent i ν) hM hU J I n hs ht σ
    (pointGeometricSourceJacquet_subsingleton_of_cuspidal
      i ν hN hZ actual hLength hSimple hStandard hInter hG hi hν hM hU
      I J w hw n hn hs σ hc hproper)

end RationalPointFamily

end Langlands.Aubert.General
