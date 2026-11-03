import Langlands.Representation.Aubert.General.RationalTargetInductionComparison

/-! # Actual normalized rational geometric terms -/

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
  [TopologicalSpace k]

local instance rationalGeometricTermPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
  (hM : ∀ K, IsClosed (levi i ν K : Set (RationalPoint k G.X)))
  (hU : ∀ K, IsClosed (unipotent i ν K : Set (RationalPoint k G.X)))
  (hP : ∀ K, IsClosed (parabolic i ν K : Set (RationalPoint k G.X)))
  (hproj : ∀ K : Finset I,
    Continuous (standardLeviProjection i ν hInter hG hi hν I K))
  (hiFl : letI := (hM I).locallyCompactSpace
    ∀ K : Finset I, PreservesFiniteLength
      (normalizedInductionFunctor.{u, max (u + 1) v}
        (isSemidirectDecomposition_in_levi i ν hInter hG hi hν I K)
        ((hU (leviIndex I K)).preimage continuous_subtype_val)))

variable
  (hUc : ∀ K : Finset J, Jacquet.Localization.IsLimitOfCompactSubgroups
    ((unipotent i ν (leviIndex J K)).subgroupOf (levi i ν J)))
  (hrFl : letI := (hM J).locallyCompactSpace
    ∀ K : Finset J, PreservesFiniteLength
      (jacquetFunctor.{u, max (u + 1) v}
        (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J K)
        ((hU (leviIndex J K)).preimage continuous_subtype_val)))

include hP hproj hiFl hUc hrFl in
/-- All four preservation properties of the actual geometric term follow from
literal restricted induction and Jacquet preservation and topological exactness. -/
theorem pointGeometricTermFiniteLength :
    GeometricTermFiniteLength.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν) hM hU I J (n : rationalPoints G)
      (pointSourceDecomposition
        i ν hInter hG hi hν hN hZ cs hLevi hSource I J w hw n hn)
      (pointTargetDecomposition
        i ν hInter hG hi hν hN hZ cs hLevi hSource I J w hw n hn) := by
  have hs := pointSourceJacquetPreservation.{u, v}
    i ν hInter hG hi hν hN hZ cs hLevi hSource I J w hw n hn hM hU hUc hrFl
  have ht := pointTargetInductionPreservation.{u, v}
    i ν hInter hG hi hν hN hZ cs hLevi hSource I J w hw n hn hM hU hP hproj hiFl
  exact ⟨hs.1, hs.2, ht.1, ht.2⟩

/-- The actual source-Jacquet, lift-conjugation and target-induction term on
exact finite-length K0, with decompositions and preservation derived. -/
def pointGeometricTermK0 :
    FiniteLengthGrothendieckGroup.{0, u, max (u + 1) v} ℂ (levi i ν J) →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{0, u, max (u + 1) v} ℂ (levi i ν I) :=
  geometricTermK0.{u, u, max (u + 1) v}
    (parabolic i ν) (levi i ν) (unipotent i ν) hM hU I J (n : rationalPoints G)
    (pointSourceDecomposition
      i ν hInter hG hi hν hN hZ cs hLevi hSource I J w hw n hn)
    (pointTargetDecomposition
      i ν hInter hG hi hν hN hZ cs hLevi hSource I J w hw n hn)
    (pointGeometricTermFiniteLength
      i ν hInter hG hi hν hN hZ cs hLevi hSource I J w hw n hn
      hM hU hP hproj hiFl hUc hrFl)

/-- The constructed map is the composite of the actual source map, actual
normalizer conjugation and actual target map. -/
theorem pointGeometricTermK0_eq_composite :
    pointGeometricTermK0.{u, v}
        i ν hInter hG hi hν hN hZ cs hLevi hSource I J w hw n hn
        hM hU hP hproj hiFl hUc hrFl =
      (pointTargetInductionK0.{u, v}
        i ν hInter hG hi hν hN hZ cs hLevi hSource I J w hw n hn
        hM hU hP hproj hiFl).comp
        ((conjugationK0.{u, max (u + 1) v} (n : rationalPoints G)
          (geometricIntersectionMembership (levi i ν I) (levi i ν J)
            (n : rationalPoints G))).comp
          (pointSourceJacquetK0.{u, v}
            i ν hInter hG hi hν hN hZ cs hLevi hSource I J w hw n hn
            hM hU hUc hrFl)) := rfl

end Langlands.Aubert.General.RationalPointFamily
