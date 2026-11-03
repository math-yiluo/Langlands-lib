import Langlands.Representation.Aubert.General.RationalSourceJacquet

/-! # The actual rational source map in the literal Levi family -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep
open Group.RelativeWeylIndexing
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

include hN hZ cs hLevi hSource hw hn in
/-- The actual source Levi is the literal ambient Levi at the restricted index. -/
theorem pointSourceLeviIdentity :
    geometricSourceIntersection (levi i ν I) (levi i ν J) (n : rationalPoints G) =
      levi i ν (leviIndex J
        (intersectionLeviIndex (pointCoxeterSystem i ν hN hZ cs) I J w)) := by
  rw [leviIndex_intersectionLeviIndex]
  exact (point_geometricSourceIntersections
    i ν hN hZ cs hLevi hSource I J w hw n hn).1

include hN hZ cs hLevi hSource hw hn in
/-- The standard source Levi lies in `L_J`, as follows from the actual intersection. -/
theorem pointSourceLeviInclusion :
    levi i ν (leviIndex J
      (intersectionLeviIndex (pointCoxeterSystem i ν hN hZ cs) I J w)) ≤
        levi i ν J := by
  rw [← pointSourceLeviIdentity i ν hN hZ cs hLevi hSource I J w hw n hn]
  exact inf_le_left

section Topology

variable [TopologicalSpace k]

local instance rationalSourceComparisonPointTopology :
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

/-- The actual source Jacquet map with its codomain identified with the literal
standard Levi at the intersection labels. -/
def pointStandardizedSourceJacquetK0 :
    FiniteLengthGrothendieckGroup.{0, u, max (u + 1) v} ℂ (levi i ν J) →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{0, u, max (u + 1) v} ℂ
        (levi i ν (leviIndex J
          (intersectionLeviIndex (pointCoxeterSystem i ν hN hZ cs) I J w))) :=
  (conjugationK0.{u, max (u + 1) v} 1
    (identityConjugationMembership
      (pointSourceLeviIdentity i ν hN hZ cs hLevi hSource I J w hw n hn))).comp
    (pointSourceJacquetK0 i ν hInter hG hi hν hN hZ cs hLevi hSource
      I J w hw n hn hM hU hUc hrFl)

include hUc hrFl in
/-- The complete actual source map is the literal restricted normalized Jacquet
map, transported from its subgroupOf Levi. Both preservation witnesses are derived. -/
theorem pointStandardizedSourceJacquetK0_eq :
    let _ := (hM J).locallyCompactSpace
    let K := intersectionLeviIndex (pointCoxeterSystem i ν hN hZ cs) I J w
    pointStandardizedSourceJacquetK0.{u, v} i ν hInter hG hi hν hN hZ cs hLevi hSource
      I J w hw n hn hM hU hUc hrFl =
      (FiniteLengthGrothendieckGroup.pullback
        (subgroupOfContinuousEquiv
          (pointSourceLeviInclusion i ν hN hZ cs hLevi hSource I J w hw n hn)).symm).comp
        (jacquetK0.{u, max (u + 1) v}
          (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J K)
          ((hU (leviIndex J K)).preimage continuous_subtype_val)
          (hrFl K)
          (jacquetFunctor_preservesShortExact
            (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J K)
            ((hU (leviIndex J K)).preimage continuous_subtype_val) (hUc K))) := by
  let _ := (hM J).locallyCompactSpace
  let K := intersectionLeviIndex (pointCoxeterSystem i ν hN hZ cs) I J w
  have hRad := (point_geometricSourceIntersections
    i ν hN hZ cs hLevi hSource I J w hw n hn).2.2
  rw [← leviIndex_intersectionLeviIndex
    (pointCoxeterSystem i ν hN hZ cs) I J w] at hRad
  exact geometricSourceJacquetK0OfEq.{u, u, max (u + 1) v}
    (parabolic i ν) (levi i ν) (unipotent i ν) hM hU I J (leviIndex J K)
    (n : rationalPoints G)
    (pointSourceDecomposition i ν hInter hG hi hν hN hZ cs hLevi hSource I J w hw n hn)
    (pointSourceLeviInclusion i ν hN hZ cs hLevi hSource I J w hw n hn)
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J K)
    (pointSourceLeviIdentity i ν hN hZ cs hLevi hSource I J w hw n hn) hRad
    ⟨hrFl K, jacquetFunctor_preservesShortExact
      (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J K)
      ((hU (leviIndex J K)).preimage continuous_subtype_val) (hUc K)⟩

end Topology

end Langlands.Aubert.General.RationalPointFamily
