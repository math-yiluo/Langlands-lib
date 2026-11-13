import Langlands.Representation.Aubert.General.Corollary110aAssembly
import Langlands.Representation.Aubert.General.RationalLeviFiniteLengthProof
import Langlands.Representation.Aubert.General.RationalInvolutivityReduction
import Langlands.Representation.Aubert.General.RationalCorollaryTargets
import Langlands.Representation.Aubert.General.RationalInductionK0Assembly
import Langlands.Representation.Aubert.General.RationalGeometricK0Expansion

/-! # Corollary 1.10(a) on the actual rational-point family from induction compatibility -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance rationalCorollary110aPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

/-- Corollary 1.10(a) for one actual standard family, from the published
rational induction compatibility and finite length of normalized induction
inside the closed standard Levis. Every other inside-Levi premise of the
compatibility statement is derived from the displayed premises of the
corollary; Jacquet finite length inside the Levis is
`standardLeviJacquet_preservesFiniteLength`. -/
theorem rationalCorollary110a_of_inductionCompatibility
    (hcompat : RationalInductionCompatibilityStatement.{u, v})
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    [Mono i.hom.hom.left]
    [LocallyCompactSpace (RationalPoint k G.X)]
    [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
    (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    (hStandard : StandardCocharacterStatement.{u})
    (hInter : StandardLeviIntersectionStatement.{u}) (hRoots : HasRelativeRootSystem i)
    (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
    (hM : ∀ J, IsClosed (levi i ν J : Set (RationalPoint k G.X)))
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
    (hiLFl : ∀ J, letI := (hM J).locallyCompactSpace
      ∀ I : Finset J, PreservesFiniteLength
        (normalizedInductionFunctor.{u, max (u + 1) v}
          (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I)
          ((hU (leviIndex J I)).preimage continuous_subtype_val))) :
    letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
    letI : DecidableEq (SimpleRoot i ν) := Classical.decEq _
    corollary110a.{u, u, max (u + 1) v}
      (P := parabolic i ν) (M := levi i ν) (U := unipotent i ν)
      (h := isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν) (hU := hU)
      (hfl := standardParabolicFiniteLength
        i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl)
      (hM := hM) (hLevi := isSemidirectDecomposition_in_levi i ν hInter hG hi hν) := by
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  let : DecidableEq (SimpleRoot i ν) := Classical.decEq _
  have hrLFl := fun J => standardLeviJacquet_preservesFiniteLength.{u, v}
    i ν hInter hG hi hν hStandard hU hproj hUc hiFl hrFl J (hM J)
  exact corollary110a_of_inductionCompatibility (parabolic i ν) (levi i ν) (unipotent i ν)
    (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν) hU
    (standardParabolicFiniteLength i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl) hM
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν)
    (standardLeviParabolicFiniteLength_of_premises i ν hStandard hG hi hν hU hP hproj hUc
      hInter hiLFl hrLFl)
    (inductionCompatibilityStatement_of_rational i ν hStandard hG hi hν hU hP hproj hUc
      hiFl hrFl hRoots hInter hiLFl hrLFl hcompat)

/-- The exact proposition `RationalCorollary110aStatement`, from rational
induction compatibility. Inside-Levi finite length is supplied by
`rationalLeviFiniteLengthStatement`. -/
theorem rationalCorollary110aStatement_of_inductionCompatibility
    (hcompat : RationalInductionCompatibilityStatement.{u, v}) :
    RationalCorollary110aStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  intro _ _ _ ν hν hStandard hInter hRoots hU hM hP hproj hUc hiFl hrFl
  exact rationalCorollary110a_of_inductionCompatibility hcompat hG i hi ν hν hStandard
    hInter hRoots hU hM hP hproj hUc hiFl hrFl
    (fun J I => (rationalLeviFiniteLengthStatement k G hG T i hi ν hν hStandard hInter
      hU hP hproj hUc hiFl hrFl hM J I).1)

set_option linter.defProp false in
/-- An internal proof adapter from rational induction compatibility to the
whole rational Corollary 1.10(a) proposition. It retains compatibility as its
input and does not provide an unconditional proof of the corollary. -/
def rationalCorollary110aOfInductionCompatibility :
    RationalInductionCompatibilityStatement.{u, v} → RationalCorollary110aStatement.{u, v} :=
  rationalCorollary110aStatement_of_inductionCompatibility

/-- The exact proposition `RationalCorollary110aStatement`, from rational
induced Weyl conjugacy. Induction compatibility is assembled from it and the
published geometric-lemma expansion `rationalGeometricK0Expansion`. -/
theorem rationalCorollary110aStatement_of_inducedK0WeylConjugacy
    (hWeyl : RationalInducedK0WeylConjugacyStatement.{u, v}) :
    RationalCorollary110aStatement.{u, v} :=
  rationalCorollary110aStatement_of_inductionCompatibility
    (rationalInductionCompatibility_of_expansion_and_inducedWeyl
      ⟨rationalGeometricK0Expansion, hWeyl⟩)

end Langlands.Aubert.General.RationalPointFamily
