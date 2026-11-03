import Langlands.Representation.Aubert.General.RationalPointInducedTerm
import Langlands.Representation.Aubert.General.RationalPointSourceGeometry
import Langlands.Representation.Aubert.General.RationalSuppliedCoxeterComparisons
import Langlands.Representation.Aubert.General.RationalWeylComparisonProof
import Langlands.Representation.Aubert.General.RationalGeometricK0Target
import Langlands.Representation.Aubert.General.RationalInducedWeylConjugacyTarget

/-! # Rational induction compatibility from the two representation identities -/

noncomputable section

open Classical

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

/-- The two separately published representation-theoretic targets sufficient
for the exact rational induction-compatibility target. Neither is proved here. -/
def RationalInductionAssemblyPremises : Prop :=
  RationalGeometricK0ExpansionStatement.{u, v} ∧
    RationalInducedK0WeylConjugacyStatement.{u, v}

/-- Derive every structural, preservation, termwise and signed-sum input to
induction compatibility from the target data and these two actual identities.
The conclusion is the unchanged, unapplied published target. -/
theorem rationalInductionCompatibility_of_expansion_and_inducedWeyl
    (hInputs : RationalInductionAssemblyPremises.{u, v}) :
    RationalInductionCompatibilityStatement.{u, v} := by
  obtain ⟨hExpansion, hWeyl⟩ := hInputs
  intro k _ _ _ _ G hG T i hi
  let _ := hG.isAffineHom
  let _ := hi.isSplitSubtorus.mono
  let _ : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hRoots hInter hU hP hproj hUc hiFl hrFl
    hM hLproj hLUc hiLFl hrLFl
  dsimp only
  intro J
  let _ := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  obtain ⟨hN, hZ⟩ := rationalWeylComparison k G hG T i hi
  let c := rootSpanPointCoxeterData i ν hN hZ hG hi hRoots hν
  let _ : Finite (Weyl i) := c.finiteWeyl
  let _ : Fintype (Weyl i) := Fintype.ofFinite _
  have hSimple := positiveSimpleReflectionComparison_of_rootLength
    i ν hN hZ c.system hi.isSplitSubtorus.1 hRoots hν c.rootLength
  have hSource := pointSourceIntersectionIdentities
    i ν hN hZ c.system hStandard hG hi hν hInter c.rootLength hSimple
  let dec := isSemidirectDecomposition_of_standardCocharacterStatement
    i ν hStandard hG hi hν
  let fl := standardParabolicFiniteLength.{u, v}
    i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl
  let flL := fun A => standardLeviParabolicFiniteLength.{u, v}
    i ν hInter hG hi hν hU hP A (hM A)
      (hLproj A) (hLUc A) (hiLFl A) (hrLFl A)
  let geom := geometricIntersectionDecompositions_of_pointSource
    i ν c.system hSource hInter hG hi hν
  let termFl := fun I J w hw n hn =>
    geometricTermFiniteLength_of_pointSource.{u, v}
      i ν c.system hSource hInter hG hi hν hU hM flL I J w hw n hn
        (geom I J w hw n hn).1 (geom I J w hw n hn).2
  have hE := hExpansion k G hG T i hi ν hν hStandard hRoots
    hU hP hproj hUc hiFl hrFl hM hN hZ c.matrix c.system
      c.rootLength hSimple c.leviWeyl geom termFl
  have hW := hWeyl k G hG T i hi ν hν hStandard hU hP hproj hUc hiFl hrFl
  let lift : Weyl i → Group.RelativeWeyl.normalizer (torusPoints i) :=
    fun w => Classical.choose (QuotientGroup.mk_surjective w)
  have hlift : ∀ w, QuotientGroup.mk (lift w) = w :=
    fun w => Classical.choose_spec (QuotientGroup.mk_surjective w)
  change (alternatingOperator.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν) dec hU fl).comp
        (inductionK0 (dec J) (hU J) (fl J).1 (fl J).2.1) =
    (inductionK0 (dec J) (hU J) (fl J).1 (fl J).2.1).comp
      (leviAlternatingOperator.{u, u, max (u + 1) v}
        (parabolic i ν) (levi i ν) (unipotent i ν) J (hM J)
        (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J) hU (flL J))
  apply inductionCompatibility_of_geometricExpansion.{u, u, max (u + 1) v}
    (parabolic i ν) (levi i ν) (unipotent i ν) dec hU fl hM
    (torusPoints i) c.system geom termFl hE J lift hlift
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J) (flL J)
  intro I w
  let hw := (mem_minimalReps c.system I J w).mp w.property
  have hFine := hW
    (leviIndex J (intersectionLeviIndex c.system I J w))
    (leviIndex I (intersectionLeviIndex c.system J I w⁻¹)) (lift w)
    (pointSourceIntersectionConjugationMembership
      i ν c.system hSource I J w hw (lift w) (hlift w))
  simpa only [pointSourceInducedGeometricTermK0, inducedGeometricTerm,
    intersectionLeviIndex] using
    pointSourceInducedGeometricTermK0_eq.{u, v}
      (i := i) (ν := ν) (cs := c.system) (hSource := hSource)
      (hInter := hInter) (hG := hG) (hi := hi) (hν := hν)
      (hU := hU) (hM := hM) (hLfl := flL) (hStandard := hStandard) (hfl := fl)
      (hproj := hproj) (hUc := hUc) (hLUc := hLUc)
      (I := I) (J := J) (w := w) (hw := hw) (n := lift w) (hn := hlift w)
      hFine (geom I J w hw (lift w) (hlift w)).1
        (geom I J w hw (lift w) (hlift w)).2

end Langlands.Aubert.General.RationalPointFamily
