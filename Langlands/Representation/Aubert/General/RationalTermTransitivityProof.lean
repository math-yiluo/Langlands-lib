import Langlands.Representation.Aubert.General.TermStages
import Langlands.Representation.Aubert.General.RationalEndpoint
import Langlands.Representation.Aubert.General.RationalInductionStages
import Langlands.Representation.Aubert.General.RationalJacquetTransitivity
import Langlands.Representation.Aubert.General.RationalLeviFiniteLengthProof
import Langlands.Representation.Aubert.General.RationalInductionK0Assembly
import Langlands.Representation.Aubert.General.RationalGeometricK0Expansion
import Langlands.GroupScheme.Rational.StandardLeviIntersectionProof

/-! # Term transitivity and the top term for the actual rational standard family -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep
open Langlands.AlgebraicGeometry.PointTopology

/-- The two-sided term transitivity `i_J ∘ i^{L_J}_I ∘ r^{L_J}_I ∘ r_J = i_I ∘ r_I`
on exact K0 for the actual standard family, from actual normalized induction and
Jacquet restriction in stages. -/
theorem rationalTermTransitivity : RationalTermTransitivityStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  let _ : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hInter hU hP hproj hUc hiFl hrFl hM hLproj hLUc hiLFl hrLFl _ J I
  exact inductionK0_comp_leviTerm_comp_jacquetK0.{u, max (u + 1) v}
    (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν
      (leviIndex J I))
    (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν J)
    (hM J) (levi_le_of_subset i ν hInter hG hi hν _ J (leviIndex_subset J I))
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I)
    (hU (leviIndex J I)) (hU J)
    (standardInductionStagesIso.{u, v} i ν hInter hG hi hν hStandard hU hproj hUc J I
      (hM J) (hLUc J I))
    (standardJacquetStagesIso_of_standardProjection.{u, v} i ν hInter hG hi hν hStandard
      hU hproj J I (hM J) (hLUc J I))
    (standardParabolicFiniteLength.{u, v} i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl
      (leviIndex J I))
    (standardParabolicFiniteLength.{u, v} i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl J)
    (standardLeviParabolicFiniteLength.{u, v} i ν hInter hG hi hν hU hP J (hM J)
      (hLproj J) (hLUc J) (hiLFl J) (hrLFl J) I)

/-- The top term `i_S ∘ r_S = id` on exact K0 for the actual standard family,
for every enumeration of the simple roots. -/
theorem rationalTopTerm : RationalTopTermStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  let _ : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hU hP hproj hUc hiFl hrFl _
  exact alternatingTerm_univ_eq_id.{u, v} i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl

/-- Rational involutivity from induction compatibility, the one input of the
published reduction that is not discharged by a published proof or by the two
theorems above. -/
theorem rationalInvolutivityStatement_of_inductionCompatibility
    (hcompat : RationalInductionCompatibilityStatement.{u, v}) :
    RationalInvolutivityStatement.{u, v} :=
  rationalInvolutivityStatement_of_reductions standardLeviIntersection
    rationalLeviFiniteLengthStatement hcompat rationalTermTransitivity rationalTopTerm

/-- Rational involutivity from the two representation-theoretic targets of the
published induction-compatibility assembly: the geometric K0 expansion and
induced K0 Weyl conjugacy. -/
theorem rationalInvolutivityStatement_of_inductionAssemblyPremises
    (hInputs : RationalInductionAssemblyPremises.{u, v}) :
    RationalInvolutivityStatement.{u, v} :=
  rationalInvolutivityStatement_of_inductionCompatibility
    (rationalInductionCompatibility_of_expansion_and_inducedWeyl hInputs)

/-- Rational involutivity from induced K0 Weyl conjugacy alone; the geometric K0
expansion is the published `rationalGeometricK0Expansion`. -/
theorem rationalInvolutivityStatement_of_inducedK0WeylConjugacy
    (hWeyl : RationalInducedK0WeylConjugacyStatement.{u, v}) :
    RationalInvolutivityStatement.{u, v} :=
  rationalInvolutivityStatement_of_inductionAssemblyPremises
    ⟨rationalGeometricK0Expansion, hWeyl⟩

end Langlands.Aubert.General.RationalPointFamily
