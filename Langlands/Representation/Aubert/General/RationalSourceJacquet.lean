import Langlands.Representation.Aubert.General.RationalTwistedIntersectionTransport
import Langlands.Representation.Aubert.General.SourceJacquetReduction
import Langlands.Representation.Aubert.General.RationalLeviFiniteLength

/-! # Actual source Jacquet maps from the literal rational Levi family -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General

open Group.RelativeWeylIndexing

/-- Read the intrinsic source intersection labels as an index of `J`. -/
def intersectionLeviIndex {Index W : Type*} [Group W] {C : CoxeterMatrix Index}
    (cs : CoxeterSystem C W) (I J : Finset Index) (w : W) : Finset J := by
  classical
  exact (intersectionSubset cs I J w).subtype (· ∈ J)

/-- No label is lost when the source intersection is read inside `J`. -/
theorem leviIndex_intersectionLeviIndex {Index W : Type*} [Group W]
    {C : CoxeterMatrix Index} (cs : CoxeterSystem C W) (I J : Finset Index) (w : W) :
    leviIndex J (intersectionLeviIndex cs I J w) = intersectionSubset cs I J w := by
  classical
  exact Finset.subtype_map_of_mem fun _ ha => intersectionSubset_subset cs I J w ha

namespace RationalPointFamily

open GroupScheme SmoothRep
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hInter : StandardLeviIntersectionStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
  {C : CoxeterMatrix (SimpleRoot i ν)}
  (cs : CoxeterSystem C (relativeWeylGroup i))
  (hLevi : IsStandardLeviTwistedIntersection i ν cs)
  (hSource : IsStandardSourceTwistedIntersection i ν cs)
  (I J : Finset (SimpleRoot i ν)) (w : Group.RelativeWeyl.Weyl (torusPoints i))
  (hw : IsMinimal (pointCoxeterSystem i ν hN hZ cs) I J w)
  (n : Group.RelativeWeyl.normalizer (torusPoints i))
  (hn : QuotientGroup.mk n = w)

include hInter hG hi hν hN hZ cs hLevi hSource hw hn in
/-- The standard restricted decomposition and all three source identities
give the actual geometric source decomposition at every point lift. -/
theorem pointSourceDecomposition :
    GeometricSourceDecomposition (parabolic i ν) (levi i ν) (unipotent i ν)
      I J (n : rationalPoints G) := by
  let K := intersectionLeviIndex (pointCoxeterSystem i ν hN hZ cs) I J w
  have hK := isSemidirectDecomposition_in_levi i ν hInter hG hi hν J K
  rw [show leviIndex J K = intersectionSubset
      (pointCoxeterSystem i ν hN hZ cs) I J w from
    leviIndex_intersectionLeviIndex _ I J w] at hK
  obtain ⟨hL, hP, hU⟩ :=
    point_geometricSourceIntersections i ν hN hZ cs hLevi hSource I J w hw n hn
  exact geometricSourceDecompositionOfEq (parabolic i ν) (levi i ν) (unipotent i ν)
    I J _ (n : rationalPoints G) hK hP hL hU

section Topology

variable [TopologicalSpace k]

local instance rationalSourcePointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  (hM : ∀ K, IsClosed (levi i ν K : Set (RationalPoint k G.X)))
  (hU : ∀ K, IsClosed (unipotent i ν K : Set (RationalPoint k G.X)))
  (hUc : ∀ K : Finset J, Jacquet.Localization.IsLimitOfCompactSubgroups
    ((unipotent i ν (leviIndex J K)).subgroupOf (levi i ν J)))
  (hrFl : letI := (hM J).locallyCompactSpace
    ∀ K : Finset J, PreservesFiniteLength
      (jacquetFunctor.{u, max (u + 1) v}
        (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J K)
        ((hU (leviIndex J K)).preimage continuous_subtype_val)))

include hUc hrFl in
/-- The actual source preserves finite length and its short exact sequences
from the literal inside-Levi Jacquet premises of the rational target. -/
theorem pointSourceJacquetPreservation :
    let hs := pointSourceDecomposition
      i ν hInter hG hi hν hN hZ cs hLevi hSource I J w hw n hn
    PreservesFiniteLength (geometricSourceJacquetFunctor.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν) hM hU I J
      (n : rationalPoints G) hs) ∧
    PreservesFiniteLengthShortExact
      (geometricSourceJacquetFunctor.{u, u, max (u + 1) v}
        (parabolic i ν) (levi i ν) (unipotent i ν) hM hU I J
        (n : rationalPoints G) hs) := by
  let _ := (hM J).locallyCompactSpace
  let K := intersectionLeviIndex (pointCoxeterSystem i ν hN hZ cs) I J w
  have hlabels : leviIndex J K =
      intersectionSubset (pointCoxeterSystem i ν hN hZ cs) I J w :=
    leviIndex_intersectionLeviIndex _ I J w
  obtain ⟨hL, -, hRad⟩ :=
    point_geometricSourceIntersections i ν hN hZ cs hLevi hSource I J w hw n hn
  rw [← hlabels] at hL hRad
  have hKJ : levi i ν (leviIndex J K) ≤ levi i ν J := by
    rw [← hL]
    exact inf_le_left
  exact geometricSourceJacquetPreservationOfEq
    (parabolic i ν) (levi i ν) (unipotent i ν) hM hU I J (leviIndex J K)
    (n : rationalPoints G)
    (pointSourceDecomposition i ν hInter hG hi hν hN hZ cs hLevi hSource I J w hw n hn)
    hKJ (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J K) hL hRad
    ⟨hrFl K, jacquetFunctor_preservesShortExact
      (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J K)
      ((hU (leviIndex J K)).preimage continuous_subtype_val) (hUc K)⟩

/-- The exact-K0 map of the actual source Jacquet functor at an arbitrary
minimum point representative and arbitrary normalizer lift. -/
def pointSourceJacquetK0 :
    FiniteLengthGrothendieckGroup.{0, u, max (u + 1) v} ℂ (levi i ν J) →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{0, u, max (u + 1) v} ℂ
        (geometricSourceIntersection (levi i ν I) (levi i ν J)
          (n : rationalPoints G)) :=
  FiniteLengthGrothendieckGroup.map
    (geometricSourceJacquetFunctor.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν) hM hU I J (n : rationalPoints G)
      (pointSourceDecomposition i ν hInter hG hi hν hN hZ cs hLevi hSource I J w hw n hn))
    (pointSourceJacquetPreservation
      i ν hInter hG hi hν hN hZ cs hLevi hSource I J w hw n hn hM hU hUc hrFl).1
    (pointSourceJacquetPreservation
      i ν hInter hG hi hν hN hZ cs hLevi hSource I J w hw n hn hM hU hUc hrFl).2

end Topology

end RationalPointFamily

end Langlands.Aubert.General
