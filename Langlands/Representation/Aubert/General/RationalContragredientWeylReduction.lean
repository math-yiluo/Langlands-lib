import Langlands.Representation.Aubert.General.RationalAssociatedOppositeConjugation
import Langlands.Representation.Aubert.General.RationalFiniteLengthDuality
import Langlands.Representation.Aubert.General.RationalInducedWeylConjugacyTarget
import Langlands.Representation.Aubert.General.RationalContragredientReduction
import Langlands.Representation.Aubert.General.ContragredientWeylReduction

/-! # Rational duality reduction using actual longest lifts -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

section Family

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] (ν : cocharacterLattice T)
  (hStandard : StandardCocharacterStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)

local instance rationalContragredientWeylPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
  [Fintype (SimpleRoot i ν)] [Fintype (relativeWeylGroup i)]
  {CM : CoxeterMatrix (SimpleRoot i ν)}
  (cs : CoxeterSystem CM (relativeWeylGroup i))
  (hConj : StandardLeviConjugationStatement.{u})
  (hcs : IsRelativeWeylCoxeterRealization i ν cs)
  (hOpp : IsStandardAssociatedOppositeTransport i ν cs)
  (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))

/-- The actual opposite Jacquet object has finite length by conjugation to the
associated standard Jacquet object. No duality premise is used. -/
def associatedOppositeJacquetFiniteLengthObject
    (hrFl : ∀ I, PreservesFiniteLength
      (jacquetFunctor.{u, max (u + 1) v}
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν I) (hU I)))
    (I : Finset (SimpleRoot i ν))
    (A : FiniteLengthObject.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X)) :
    FiniteLengthObject.{0, u, max (u + 1) v} ℂ (levi i ν I) := by
  let ζ := standardCocharacterForDuality i ν hStandard hG hi hν I
  let n := longestSchemeNormalizerLift i ν cs I
  have hn : QuotientGroup.mk n = longestRep cs I :=
    longestSchemeNormalizerLift_mk i ν cs I
  exact conjugateJacquetFiniteLengthObject.{u, max (u + 1) v}
    (opposite_isSemidirectDecomposition
      i ν hStandard hG hi hν I ζ.val ζ.property)
    (isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν (associatedSubset cs I))
    (inversePointNormalizer i n : RationalPoint k G.X)
    (fun x => (associatedOpposite_mem_of_structural
      i ν cs hG hi hν hConj hcs hOpp I n hn ζ.val ζ.property x).2.1)
    (fun x => (associatedOpposite_mem_of_structural
      i ν cs hG hi hν hConj hcs hOpp I n hn ζ.val ζ.property x).2.2)
    (isClosed_oppositeUnipotent_localField i ζ.val) (hU (associatedSubset cs I))
    (hrFl (associatedSubset cs I)) A

variable
  (hP : ∀ I, IsClosed (parabolic i ν I : Set (RationalPoint k G.X)))
  (hproj : ∀ I, Continuous
    (isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν I).projection)
  (hUc : ∀ I, Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν I))
  (hiFl : ∀ I, PreservesFiniteLength
    (normalizedInductionFunctor.{u, max (u + 1) v}
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν I) (hU I)))
  (hrFl : ∀ I, PreservesFiniteLength
    (jacquetFunctor.{u, max (u + 1) v}
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν I) (hU I)))
  (hc : ContragredientPreservesFiniteLength.{u, max (u + 1) v}
    (RationalPoint k G.X))

include cs hConj hcs hOpp

set_option maxHeartbeats 800000 in
/-- The explicit closed Weyl-class, natural-duality and admissibility inputs,
together with the displayed actual structural transport, imply the original
standard-family term comparison. None of those closed inputs is proved here. -/
theorem standardContragredientTermComparison_of_schemeWeylDuality
    (hWeyl : RationalInducedClassWeylConjugacyStatement.{u, v})
    (hInd : RationalNaturalInductionDualityStatement.{u, v})
    (hJac : RationalNaturalJacquetDualityStatement.{u, v})
    (hadmG : RationalPointsFiniteLengthAdmissibleStatement.{u, max (u + 1) v})
    (hadmM : DynamicLeviFiniteLengthAdmissibleStatement.{u, max (u + 1) v}) :
    standardContragredientTermComparison
      i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl hc := by
  let ζ := standardCocharacterForDuality i ν hStandard hG hi hν
  let n := fun I => longestSchemeNormalizerLift i ν cs I
  have hmem (I : Finset (SimpleRoot i ν)) (x : RationalPoint k G.X) :=
    associatedOpposite_mem_of_structural i ν cs hG hi hν hConj hcs hOpp I (n I)
      (longestSchemeNormalizerLift_mk i ν cs I) (ζ I).val (ζ I).property x
  exact contragredientTermComparison_of_duality_of_weylConjugacy.{u, u, max (u + 1) v}
    (torusPoints i) (parabolic i ν) (levi i ν) (unipotent i ν)
    (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν)
    hU (standardParabolicFiniteLength i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl)
    (hWeyl k G hG T i hi ν hν hStandard hU hP hproj hUc hiFl hrFl)
    (compactOpenCofinal_of_nonarchimedean _) hc
    (fun I => oppositeParabolic i (ζ I).val)
    (fun I => oppositeUnipotent i (ζ I).val)
    (fun I => opposite_isSemidirectDecomposition
      i ν hStandard hG hi hν I (ζ I).val (ζ I).property)
    (fun I => isClosed_oppositeUnipotent_localField i (ζ I).val)
    (associatedSubsetEquiv cs) (card_associatedSubsetEquiv cs)
    (fun I => inversePointNormalizer i (n I))
    (fun I x => (hmem I x).1) (fun I x => (hmem I x).2.1)
    (fun I x => (hmem I x).2.2)
    (fun I A hA => finiteLengthJacquetDualityIso
      i ν hStandard hG hi hν hJac hadmG I (hU I) (ζ I).val (ζ I).property A hA)
    (fun I σ hσ => finiteLengthInductionDualityIso
      i ν hStandard hG hi hν hInd hadmM I (hU I) (hP I) (hproj I) σ hσ)

end Family

/-- Conditional implication into the unchanged closed target. The extra closed
structural and representation propositions remain proof obligations. -/
theorem rationalContragredientCommutation_of_schemeWeylDuality
    (hCox : RelativeWeylCoxeterStatement.{u})
    (hConj : StandardLeviConjugationStatement.{u})
    (hOpp : StandardAssociatedOppositeTransportStatement.{u})
    (hWeyl : RationalInducedClassWeylConjugacyStatement.{u, v})
    (hInd : RationalNaturalInductionDualityStatement.{u, v})
    (hJac : RationalNaturalJacquetDualityStatement.{u, v})
    (hadmG : RationalPointsFiniteLengthAdmissibleStatement.{u, max (u + 1) v})
    (hadmM : DynamicLeviFiniteLengthAdmissibleStatement.{u, max (u + 1) v}) :
    RationalContragredientCommutationStatement.{u, v} := by
  apply rationalContragredientCommutation_of_termComparison
  intro k _ _ _ _ G hG T i hi
  let _ := hG.isAffineHom
  let _ := hi.isSplitSubtorus.mono
  let _ : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard _hRoots hU hP hproj hUc hiFl hrFl hc
  obtain ⟨hFiniteW, hFiniteS, CM, cs, hcs⟩ := hCox k G hG T i hi ν hν
  let _ : Finite (relativeWeylGroup i) := hFiniteW
  let _ : Finite (SimpleRoot i ν) := hFiniteS
  let _ : Fintype (relativeWeylGroup i) := Fintype.ofFinite _
  let _ : Fintype (SimpleRoot i ν) := Fintype.ofFinite _
  exact standardContragredientTermComparison_of_schemeWeylDuality
    i ν hStandard hG hi hν cs hConj hcs
    (hOpp k G hG T i hi ν hν CM cs hcs)
    hU hP hproj hUc hiFl hrFl hc hWeyl hInd hJac hadmG hadmM

end Langlands.Aubert.General.RationalPointFamily
