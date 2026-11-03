import Langlands.Representation.Aubert.General.RationalSourceJacquetComparison

/-! # Actual target intersections in the rational standard Levi family -/

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
/-- The target intersections are the source intersections at the inverse lift,
with the two finite subsets exchanged. -/
theorem point_geometricTargetIntersections :
    let K := intersectionSubset (pointCoxeterSystem i ν hN hZ cs) J I w⁻¹
    geometricTargetIntersection (levi i ν I) (levi i ν J) (n : rationalPoints G) =
        levi i ν K ∧
      (geometricTargetIntersection (levi i ν I) (parabolic i ν J)
        (n : rationalPoints G)).subgroupOf (levi i ν I) =
          (parabolic i ν K).subgroupOf (levi i ν I) ∧
      (geometricTargetIntersection (levi i ν I) (unipotent i ν J)
        (n : rationalPoints G)).subgroupOf (levi i ν I) =
          (unipotent i ν K).subgroupOf (levi i ν I) := by
  have hn' : QuotientGroup.mk n⁻¹ = w⁻¹ := by
    rw [QuotientGroup.mk_inv, hn]
  simpa only [geometricSourceIntersection, geometricTargetIntersection,
    Subgroup.coe_inv, inv_inv] using
    point_geometricSourceIntersections i ν hN hZ cs hLevi hSource
      J I w⁻¹ (isMinimal_inv _ hw) n⁻¹ hn'

include hInter hG hi hν hN hZ cs hLevi hSource hw hn in
/-- The actual target decomposition is derived from the standard restricted
decomposition at the reversed intersection index. -/
theorem pointTargetDecomposition :
    GeometricTargetDecomposition (parabolic i ν) (levi i ν) (unipotent i ν)
      I J (n : rationalPoints G) := by
  have hn' : QuotientGroup.mk n⁻¹ = w⁻¹ := by
    rw [QuotientGroup.mk_inv, hn]
  simpa only [GeometricSourceDecomposition, GeometricTargetDecomposition,
    geometricSourceIntersection, geometricTargetIntersection,
    Subgroup.coe_inv, inv_inv] using
    pointSourceDecomposition i ν hInter hG hi hν hN hZ cs hLevi hSource
      J I w⁻¹ (isMinimal_inv _ hw) n⁻¹ hn'

include hInter hG hi hν hN hZ cs hLevi hSource in
/-- Both actual decompositions hold at every minimum representative and lift. -/
theorem pointGeometricIntersectionDecompositions :
    GeometricIntersectionDecompositions (parabolic i ν) (levi i ν) (unipotent i ν)
      (torusPoints i) (pointCoxeterSystem i ν hN hZ cs) := by
  intro I J w hw n hn
  exact ⟨pointSourceDecomposition
      i ν hInter hG hi hν hN hZ cs hLevi hSource I J w hw n hn,
    pointTargetDecomposition
      i ν hInter hG hi hν hN hZ cs hLevi hSource I J w hw n hn⟩

include hN hZ cs hLevi hSource hw hn in
/-- The actual target Levi has the literal restricted index inside `I`. -/
theorem pointTargetLeviIdentity :
    geometricTargetIntersection (levi i ν I) (levi i ν J) (n : rationalPoints G) =
      levi i ν (leviIndex I
        (intersectionLeviIndex (pointCoxeterSystem i ν hN hZ cs) J I w⁻¹)) := by
  rw [leviIndex_intersectionLeviIndex]
  exact (point_geometricTargetIntersections
    i ν hN hZ cs hLevi hSource I J w hw n hn).1

include hN hZ cs hLevi hSource hw hn in
/-- The standard target Levi lies in `L_I` by its actual intersection identity. -/
theorem pointTargetLeviInclusion :
    levi i ν (leviIndex I
      (intersectionLeviIndex (pointCoxeterSystem i ν hN hZ cs) J I w⁻¹)) ≤
        levi i ν I := by
  rw [← pointTargetLeviIdentity i ν hN hZ cs hLevi hSource I J w hw n hn]
  exact inf_le_left

include hN hZ cs hLevi hSource hw hn in
/-- The actual lift conjugates the two identified standard intersection Levis. -/
theorem pointIntersectionConjugationMembership :
    ∀ x : rationalPoints G,
      x ∈ levi i ν (leviIndex I
        (intersectionLeviIndex (pointCoxeterSystem i ν hN hZ cs) J I w⁻¹)) ↔
      (n : rationalPoints G)⁻¹ * x * (n : rationalPoints G) ∈
        levi i ν (leviIndex J
          (intersectionLeviIndex (pointCoxeterSystem i ν hN hZ cs) I J w)) := by
  intro x
  rw [← pointTargetLeviIdentity i ν hN hZ cs hLevi hSource I J w hw n hn,
    ← pointSourceLeviIdentity i ν hN hZ cs hLevi hSource I J w hw n hn]
  exact geometricIntersectionMembership (levi i ν I) (levi i ν J) (n : rationalPoints G) x

section Topology

variable [TopologicalSpace k]

local instance rationalTargetPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [NonarchimedeanGroup (RationalPoint k G.X)]

/-- Actual inverse conjugation, as a continuous equivalence of the literal
standard source and target intersection Levis. -/
def pointIntersectionConjugationEquiv :
    levi i ν (leviIndex I
      (intersectionLeviIndex (pointCoxeterSystem i ν hN hZ cs) J I w⁻¹)) ≃ₜ*
    levi i ν (leviIndex J
      (intersectionLeviIndex (pointCoxeterSystem i ν hN hZ cs) I J w)) :=
  conjugationEquiv (n : rationalPoints G)
    (pointIntersectionConjugationMembership i ν hN hZ cs hLevi hSource I J w hw n hn)

@[simp]
theorem pointIntersectionConjugationEquiv_apply
    (x : levi i ν (leviIndex I
      (intersectionLeviIndex (pointCoxeterSystem i ν hN hZ cs) J I w⁻¹))) :
    (pointIntersectionConjugationEquiv i ν hN hZ cs hLevi hSource I J w hw n hn x :
      rationalPoints G) = (n : rationalPoints G)⁻¹ * (x : rationalPoints G) *
        (n : rationalPoints G) :=
  rfl

variable [LocallyCompactSpace (RationalPoint k G.X)]
  (hM : ∀ K, IsClosed (levi i ν K : Set (RationalPoint k G.X)))
  (hU : ∀ K, IsClosed (unipotent i ν K : Set (RationalPoint k G.X)))

/-- The actual normalized target induction functor with its decomposition
derived from the literal rational standard family. -/
def pointTargetInductionFunctor :
    SmoothRep.{0, u, max (u + 1) v} ℂ
      (geometricTargetIntersection (levi i ν I) (levi i ν J) (n : rationalPoints G)) ⥤
    SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν I) :=
  geometricTargetInductionFunctor.{u, u, max (u + 1) v}
    (parabolic i ν) (levi i ν) (unipotent i ν) hM hU I J (n : rationalPoints G)
    (pointTargetDecomposition i ν hInter hG hi hν hN hZ cs hLevi hSource I J w hw n hn)

end Topology

end Langlands.Aubert.General.RationalPointFamily
