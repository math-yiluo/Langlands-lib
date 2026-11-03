import Langlands.Representation.Aubert.General.RationalTargetInduction
import Langlands.Representation.Aubert.General.TargetInductionReduction

/-! # The actual rational target map in the literal Levi family -/

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

local instance rationalTargetComparisonPointTopology :
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

include hP hproj hiFl in
/-- The actual target induction preserves finite length and short exact
sequences, from the literal inside-Levi premises of the rational target. -/
theorem pointTargetInductionPreservation :
    PreservesFiniteLength
      (pointTargetInductionFunctor.{u, v}
        i ν hInter hG hi hν hN hZ cs hLevi hSource I J w hw n hn hM hU) ∧
    PreservesFiniteLengthShortExact
      (pointTargetInductionFunctor.{u, v}
        i ν hInter hG hi hν hN hZ cs hLevi hSource I J w hw n hn hM hU) := by
  let _ := (hM I).locallyCompactSpace
  let K := intersectionLeviIndex (pointCoxeterSystem i ν hN hZ cs) J I w⁻¹
  have hPar := (point_geometricTargetIntersections
    i ν hN hZ cs hLevi hSource I J w hw n hn).2.1
  have hRad := (point_geometricTargetIntersections
    i ν hN hZ cs hLevi hSource I J w hw n hn).2.2
  rw [← leviIndex_intersectionLeviIndex
    (pointCoxeterSystem i ν hN hZ cs) J I w⁻¹] at hPar hRad
  exact geometricTargetInductionPreservationOfEq.{u, u, max (u + 1) v}
    (parabolic i ν) (levi i ν) (unipotent i ν) hM hU I J (leviIndex I K)
    (n : rationalPoints G)
    (pointTargetDecomposition i ν hInter hG hi hν hN hZ cs hLevi hSource I J w hw n hn)
    (pointTargetLeviInclusion i ν hN hZ cs hLevi hSource I J w hw n hn)
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν I K)
    (pointTargetLeviIdentity i ν hN hZ cs hLevi hSource I J w hw n hn) hPar hRad
    (restrictedInductionPreservation i ν hInter hG hi hν I hM hU hP hproj hiFl K)

/-- The actual target-intersection induction on exact finite-length K0,
with both preservation witnesses derived from the literal standard family. -/
def pointTargetInductionK0 :
    FiniteLengthGrothendieckGroup.{0, u, max (u + 1) v} ℂ
        (geometricTargetIntersection (levi i ν I) (levi i ν J)
          (n : rationalPoints G)) →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{0, u, max (u + 1) v} ℂ (levi i ν I) :=
  FiniteLengthGrothendieckGroup.map
    (pointTargetInductionFunctor.{u, v}
      i ν hInter hG hi hν hN hZ cs hLevi hSource I J w hw n hn hM hU)
    (pointTargetInductionPreservation
      i ν hInter hG hi hν hN hZ cs hLevi hSource I J w hw n hn hM hU hP hproj hiFl).1
    (pointTargetInductionPreservation
      i ν hInter hG hi hν hN hZ cs hLevi hSource I J w hw n hn hM hU hP hproj hiFl).2

include hP hproj hiFl in
/-- The complete actual target map is literal restricted normalized induction
after the canonical subgroupOf transport and identity Levi identification. -/
theorem pointTargetInductionK0_eq :
    let _ := (hM I).locallyCompactSpace
    let K := intersectionLeviIndex (pointCoxeterSystem i ν hN hZ cs) J I w⁻¹
    let hfl := restrictedInductionPreservation
      i ν hInter hG hi hν I hM hU hP hproj hiFl K
    pointTargetInductionK0.{u, v}
        i ν hInter hG hi hν hN hZ cs hLevi hSource I J w hw n hn hM hU hP hproj hiFl =
      ((inductionK0.{u, max (u + 1) v}
        (isSemidirectDecomposition_in_levi i ν hInter hG hi hν I K)
        ((hU (leviIndex I K)).preimage continuous_subtype_val) hfl.1 hfl.2).comp
        (FiniteLengthGrothendieckGroup.pullback
          (subgroupOfContinuousEquiv
            (pointTargetLeviInclusion i ν hN hZ cs hLevi hSource I J w hw n hn)))).comp
        (conjugationK0.{u, max (u + 1) v} 1
          (identityConjugationMembership
            (pointTargetLeviIdentity i ν hN hZ cs hLevi hSource I J w hw n hn))) := by
  let _ := (hM I).locallyCompactSpace
  let K := intersectionLeviIndex (pointCoxeterSystem i ν hN hZ cs) J I w⁻¹
  have hPar := (point_geometricTargetIntersections
    i ν hN hZ cs hLevi hSource I J w hw n hn).2.1
  have hRad := (point_geometricTargetIntersections
    i ν hN hZ cs hLevi hSource I J w hw n hn).2.2
  rw [← leviIndex_intersectionLeviIndex
    (pointCoxeterSystem i ν hN hZ cs) J I w⁻¹] at hPar hRad
  exact geometricTargetInductionK0OfEq.{u, u, max (u + 1) v}
    (parabolic i ν) (levi i ν) (unipotent i ν) hM hU I J (leviIndex I K)
    (n : rationalPoints G)
    (pointTargetDecomposition i ν hInter hG hi hν hN hZ cs hLevi hSource I J w hw n hn)
    (pointTargetLeviInclusion i ν hN hZ cs hLevi hSource I J w hw n hn)
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν I K)
    (pointTargetLeviIdentity i ν hN hZ cs hLevi hSource I J w hw n hn) hPar hRad
    (restrictedInductionPreservation i ν hInter hG hi hν I hM hU hP hproj hiFl K)

end Langlands.Aubert.General.RationalPointFamily
