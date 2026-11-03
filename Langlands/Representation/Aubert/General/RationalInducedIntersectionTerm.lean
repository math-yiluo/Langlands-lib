import Langlands.Representation.Aubert.General.InducedIntersectionTerm
import Langlands.Representation.Aubert.General.RationalGeometricTermComparison
import Langlands.Representation.Aubert.General.RationalInductionK0Stages
import Langlands.Representation.Aubert.General.RationalInductionTarget

/-! # Induced rational geometric terms and source alternating terms -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep
open Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [TopologicalSpace k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hInter : StandardLeviIntersectionStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (hStandard : StandardCocharacterStatement.{u})
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
  {C : CoxeterMatrix (SimpleRoot i ν)}
  (cs : CoxeterSystem C (relativeWeylGroup i))
  (hLevi : IsStandardLeviTwistedIntersection i ν cs)
  (hSource : IsStandardSourceTwistedIntersection i ν cs)
  (I J : Finset (SimpleRoot i ν)) (w : Group.RelativeWeyl.Weyl (torusPoints i))
  (hw : IsMinimal (pointCoxeterSystem i ν hN hZ cs) I J w)
  (n : Group.RelativeWeyl.normalizer (torusPoints i))
  (hn : QuotientGroup.mk n = w)

local instance rationalInducedIntersectionTermPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
  (hM : ∀ A, IsClosed (levi i ν A : Set (RationalPoint k G.X)))
  (hU : ∀ A, IsClosed (unipotent i ν A : Set (RationalPoint k G.X)))
  (hP : ∀ A, IsClosed (parabolic i ν A : Set (RationalPoint k G.X)))
  (hproj : ∀ A, Continuous
    (isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν A).projection)
  (hUc : ∀ A, Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν A))
  (hiFl : ∀ A, PreservesFiniteLength
    (normalizedInductionFunctor.{u, max (u + 1) v}
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν A) (hU A)))
  (hrFl : ∀ A, PreservesFiniteLength
    (jacquetFunctor.{u, max (u + 1) v}
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν A) (hU A)))
  (hLproj : ∀ (A : Finset (SimpleRoot i ν)) (K : Finset A),
    Continuous (standardLeviProjection i ν hInter hG hi hν A K))
  (hLUc : ∀ (A : Finset (SimpleRoot i ν)) (K : Finset A),
    Jacquet.Localization.IsLimitOfCompactSubgroups
      ((unipotent i ν (leviIndex A K)).subgroupOf (levi i ν A)))
  (hiLFl : ∀ A, letI := (hM A).locallyCompactSpace
    ∀ K : Finset A, PreservesFiniteLength
      (normalizedInductionFunctor.{u, max (u + 1) v}
        (isSemidirectDecomposition_in_levi i ν hInter hG hi hν A K)
        ((hU (leviIndex A K)).preimage continuous_subtype_val)))
  (hrLFl : ∀ A, letI := (hM A).locallyCompactSpace
    ∀ K : Finset A, PreservesFiniteLength
      (jacquetFunctor.{u, max (u + 1) v}
        (isSemidirectDecomposition_in_levi i ν hInter hG hi hν A K)
        ((hU (leviIndex A K)).preimage continuous_subtype_val)))

/-- Actual ambient induction of the complete rational geometric term. -/
def pointInducedGeometricTermK0 :
    FiniteLengthGrothendieckGroup.{0, u, max (u + 1) v} ℂ (levi i ν J) →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X) :=
  (inductionK0.{u, max (u + 1) v} ((isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν) I) (hU I) ((standardParabolicFiniteLength.{u, v} i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl) I).1 ((standardParabolicFiniteLength.{u, v} i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl) I).2.1).comp
    (pointGeometricTermK0.{u, v}
      i ν hInter hG hi hν hN hZ cs hLevi hSource I J w hw n hn
      hM hU hP (hLproj I) (hiLFl I) (hLUc J) (hrLFl J))

variable [ValuativeRel k] [IsNonarchimedeanLocalField k]
  (hWeyl :
    (inductionK0.{u, max (u + 1) v}
      ((isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν) (leviIndex I (intersectionLeviIndex (pointCoxeterSystem i ν hN hZ cs) J I w⁻¹))) (hU (leviIndex I (intersectionLeviIndex (pointCoxeterSystem i ν hN hZ cs) J I w⁻¹)))
      ((standardParabolicFiniteLength.{u, v} i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl) (leviIndex I (intersectionLeviIndex (pointCoxeterSystem i ν hN hZ cs) J I w⁻¹))).1 ((standardParabolicFiniteLength.{u, v} i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl) (leviIndex I (intersectionLeviIndex (pointCoxeterSystem i ν hN hZ cs) J I w⁻¹))).2.1).comp
        (conjugationK0.{u, max (u + 1) v} (n : rationalPoints G)
          (pointIntersectionConjugationMembership
            i ν hN hZ cs hLevi hSource I J w hw n hn)) =
    inductionK0.{u, max (u + 1) v}
      ((isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν) (leviIndex J (intersectionLeviIndex (pointCoxeterSystem i ν hN hZ cs) I J w))) (hU (leviIndex J (intersectionLeviIndex (pointCoxeterSystem i ν hN hZ cs) I J w)))
      ((standardParabolicFiniteLength.{u, v} i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl) (leviIndex J (intersectionLeviIndex (pointCoxeterSystem i ν hN hZ cs) I J w))).1 ((standardParabolicFiniteLength.{u, v} i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl) (leviIndex J (intersectionLeviIndex (pointCoxeterSystem i ν hN hZ cs) I J w))).2.1)

include hWeyl in
/-- Actual rational stages and fine-Levi induced Weyl equality identify every
induced geometric term with its literal source alternating term. -/
theorem pointInducedGeometricTermK0_eq :
    pointInducedGeometricTermK0.{u, v}
      i ν hInter hG hi hν hStandard hN hZ cs hLevi hSource I J w hw n hn
      hM hU hP hproj hUc hiFl hrFl hLproj hLUc hiLFl hrLFl =
    inducedLeviAlternatingTerm.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν) (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν) hU (standardParabolicFiniteLength.{u, v} i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl) hM J
      (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J)
      (standardLeviParabolicFiniteLength.{u, v}
        i ν hInter hG hi hν hU hP J (hM J)
        (hLproj J) (hLUc J) (hiLFl J) (hrLFl J)) (intersectionLeviIndex (pointCoxeterSystem i ν hN hZ cs) I J w) := by
  let _ := (hM J).locallyCompactSpace
  let _ := (hM I).locallyCompactSpace
  have hS := standardInductionStagesIso.{u, v}
    i ν hInter hG hi hν hStandard hU hproj hUc J (intersectionLeviIndex (pointCoxeterSystem i ν hN hZ cs) I J w)
    (hM J) (hLUc J (intersectionLeviIndex (pointCoxeterSystem i ν hN hZ cs) I J w))
  have hT := standardInductionStagesIso.{u, v}
    i ν hInter hG hi hν hStandard hU hproj hUc I (intersectionLeviIndex (pointCoxeterSystem i ν hN hZ cs) J I w⁻¹)
    (hM I) (hLUc I (intersectionLeviIndex (pointCoxeterSystem i ν hN hZ cs) J I w⁻¹))
  have hTargetFl := standardLeviParabolicFiniteLength.{u, v}
    i ν hInter hG hi hν hU hP I (hM I)
    (hLproj I) (hLUc I) (hiLFl I) (hrLFl I) (intersectionLeviIndex (pointCoxeterSystem i ν hN hZ cs) J I w⁻¹)
  have hterm := inducedStandardIntersectionTermK0_eq.{u, u, max (u + 1) v}
    (parabolic i ν) (levi i ν) (unipotent i ν) (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν) hU (standardParabolicFiniteLength.{u, v} i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl) hM
    I J (intersectionLeviIndex (pointCoxeterSystem i ν hN hZ cs) I J w) (intersectionLeviIndex (pointCoxeterSystem i ν hN hZ cs) J I w⁻¹) (n : rationalPoints G)
    (pointSourceLeviInclusion i ν hN hZ cs hLevi hSource I J w hw n hn)
    (pointTargetLeviInclusion i ν hN hZ cs hLevi hSource I J w hw n hn)
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J)
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν I (intersectionLeviIndex (pointCoxeterSystem i ν hN hZ cs) J I w⁻¹))
    (pointIntersectionConjugationMembership
      i ν hN hZ cs hLevi hSource I J w hw n hn)
    (standardLeviParabolicFiniteLength.{u, v}
      i ν hInter hG hi hν hU hP J (hM J)
      (hLproj J) (hLUc J) (hiLFl J) (hrLFl J))
    ⟨hTargetFl.1, hTargetFl.2.1⟩ hS hT hWeyl
  unfold pointInducedGeometricTermK0
  rw [pointGeometricTermK0_eq_standard]
  exact hterm

end Langlands.Aubert.General.RationalPointFamily
