import Langlands.Representation.Aubert.General.RationalGeometricTerm
import Langlands.Representation.Aubert.General.GeometricTermReduction

/-! # Rational geometric terms in the literal standard family -/

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

local instance rationalGeometricTermComparisonPointTopology :
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

include hP hproj hiFl in
private theorem restrictedInductionPreservation (K : Finset I) :
    letI := (hM I).locallyCompactSpace
    PreservesFiniteLength (normalizedInductionFunctor.{u, max (u + 1) v}
      (isSemidirectDecomposition_in_levi i ν hInter hG hi hν I K)
      ((hU (leviIndex I K)).preimage continuous_subtype_val)) ∧
    PreservesFiniteLengthShortExact
      (normalizedInductionFunctor.{u, max (u + 1) v}
        (isSemidirectDecomposition_in_levi i ν hInter hG hi hν I K)
        ((hU (leviIndex I K)).preimage continuous_subtype_val)) := by
  let _ := (hM I).locallyCompactSpace
  exact ⟨hiFl K, normalizedInductionFunctor_preservesShortExact
    (compactOpenCofinal_of_nonarchimedean _)
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν I K)
    ((hU (leviIndex I K)).preimage continuous_subtype_val)
    ((hP (leviIndex I K)).preimage continuous_subtype_val) (hproj K)⟩

omit [T2Space (RationalPoint k G.X)] in
include hUc hrFl in
private theorem restrictedJacquetPreservation (K : Finset J) :
    letI := (hM J).locallyCompactSpace
    PreservesFiniteLength (jacquetFunctor.{u, max (u + 1) v}
      (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J K)
      ((hU (leviIndex J K)).preimage continuous_subtype_val)) ∧
    PreservesFiniteLengthShortExact (jacquetFunctor.{u, max (u + 1) v}
      (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J K)
      ((hU (leviIndex J K)).preimage continuous_subtype_val)) := by
  let _ := (hM J).locallyCompactSpace
  exact ⟨hrFl K, jacquetFunctor_preservesShortExact
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J K)
    ((hU (leviIndex J K)).preimage continuous_subtype_val) (hUc K)⟩

/-- The literal standard restricted source and target factors, with the actual
normalizer conjugation between the two fine standard Levis. -/
def pointStandardIntersectionTermK0 :
    FiniteLengthGrothendieckGroup.{0, u, max (u + 1) v} ℂ (levi i ν J) →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{0, u, max (u + 1) v} ℂ (levi i ν I) :=
  letI := (hM J).locallyCompactSpace
  letI := (hM I).locallyCompactSpace
  let Ks := intersectionLeviIndex (pointCoxeterSystem i ν hN hZ cs) I J w
  let Kt := intersectionLeviIndex (pointCoxeterSystem i ν hN hZ cs) J I w⁻¹
  standardIntersectionTermK0.{u, u, max (u + 1) v}
    (parabolic i ν) (levi i ν) (unipotent i ν) hM hU
    I J (leviIndex J Ks) (leviIndex I Kt) (n : rationalPoints G)
    (pointSourceLeviInclusion i ν hN hZ cs hLevi hSource I J w hw n hn)
    (pointTargetLeviInclusion i ν hN hZ cs hLevi hSource I J w hw n hn)
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J Ks)
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν I Kt)
    (pointIntersectionConjugationMembership i ν hN hZ cs hLevi hSource I J w hw n hn)
    (restrictedJacquetPreservation i ν hInter hG hi hν J hM hU hUc hrFl Ks)
    (restrictedInductionPreservation i ν hInter hG hi hν I hM hU hP hproj hiFl Kt)

include hP hproj hiFl hUc hrFl in
/-- The complete actual rational geometric term equals the literal standard
restricted term for every minimum point representative and normalizer lift. -/
theorem pointGeometricTermK0_eq_standard :
    pointGeometricTermK0.{u, v}
        i ν hInter hG hi hν hN hZ cs hLevi hSource I J w hw n hn
        hM hU hP hproj hiFl hUc hrFl =
      pointStandardIntersectionTermK0.{u, v}
        i ν hInter hG hi hν hN hZ cs hLevi hSource I J w hw n hn
        hM hU hP hproj hiFl hUc hrFl := by
  let _ := (hM J).locallyCompactSpace
  let _ := (hM I).locallyCompactSpace
  let Ks := intersectionLeviIndex (pointCoxeterSystem i ν hN hZ cs) I J w
  let Kt := intersectionLeviIndex (pointCoxeterSystem i ν hN hZ cs) J I w⁻¹
  have hSourceRad := (point_geometricSourceIntersections
    i ν hN hZ cs hLevi hSource I J w hw n hn).2.2
  have hTargetPar := (point_geometricTargetIntersections
    i ν hN hZ cs hLevi hSource I J w hw n hn).2.1
  have hTargetRad := (point_geometricTargetIntersections
    i ν hN hZ cs hLevi hSource I J w hw n hn).2.2
  rw [← leviIndex_intersectionLeviIndex
    (pointCoxeterSystem i ν hN hZ cs) I J w] at hSourceRad
  rw [← leviIndex_intersectionLeviIndex
    (pointCoxeterSystem i ν hN hZ cs) J I w⁻¹] at hTargetPar hTargetRad
  exact geometricTermK0_eq_standardOfEq.{u, u, max (u + 1) v}
    (parabolic i ν) (levi i ν) (unipotent i ν) hM hU
    I J (leviIndex J Ks) (leviIndex I Kt) (n : rationalPoints G)
    (pointSourceLeviInclusion i ν hN hZ cs hLevi hSource I J w hw n hn)
    (pointTargetLeviInclusion i ν hN hZ cs hLevi hSource I J w hw n hn)
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J Ks)
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν I Kt)
    (pointIntersectionConjugationMembership i ν hN hZ cs hLevi hSource I J w hw n hn)
    (restrictedJacquetPreservation i ν hInter hG hi hν J hM hU hUc hrFl Ks)
    (restrictedInductionPreservation i ν hInter hG hi hν I hM hU hP hproj hiFl Kt)
    (pointSourceDecomposition
      i ν hInter hG hi hν hN hZ cs hLevi hSource I J w hw n hn)
    (pointTargetDecomposition
      i ν hInter hG hi hν hN hZ cs hLevi hSource I J w hw n hn)
    (pointSourceLeviIdentity i ν hN hZ cs hLevi hSource I J w hw n hn)
    hSourceRad
    (pointTargetLeviIdentity i ν hN hZ cs hLevi hSource I J w hw n hn)
    hTargetPar hTargetRad
    (pointGeometricTermFiniteLength
      i ν hInter hG hi hν hN hZ cs hLevi hSource I J w hw n hn
      hM hU hP hproj hiFl hUc hrFl)

end Langlands.Aubert.General.RationalPointFamily
