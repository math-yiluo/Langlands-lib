import Langlands.Representation.CuspidalSupport.BernsteinDecompositionInputsAssembly
import Langlands.Representation.CuspidalSupport.BernsteinInducedInertiaGeometricExclusion
import Langlands.Representation.CuspidalSupport.BernsteinDecompositionReduction

/-! # The Bernstein decomposition statements from their named inputs -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

/-- Renard VI.7.2, decomposition conjunct, from represented VI.5.2 and VI.5.4
and the two whole-category decompositions of VI.3.5. The whole-category
splitting is used at the carrier universes `uV` (for the embedding of every
representation into induced cuspidal pieces) and `max uF uV` (for the
supercuspidality of the inducing pieces). -/
theorem bernsteinDecompositionStatement_of_inputs
    (hAssociate :
      RepresentedParabolic.LeviSupercuspidalInductionAssociationStatement.{uF, max uF uV})
    (hind :
      RepresentedParabolic.LeviInductionNoSupercuspidalSubquotientStatement.{uF, max uF uV})
    (hdecomp : RationalCuspidalInertiaProductDecompositionStatement.{uF, max uF uV})
    (hwhole : RationalWholeCuspidalCategoryDecompositionStatement.{uF, uV})
    (hwhole' : RationalWholeCuspidalCategoryDecompositionStatement.{uF, max uF uV}) :
    BernsteinDecompositionStatement.{uF, uV} := by
  intro F _ _ _ _ G _ _ T i ν
  let : TopologicalSpace (rationalPoints G) := pointTopology
  intro _ _ family
  have hsc := bernsteinJacquetExclusionOfInertiaBlockSupercuspidal.{uF, uV} i ν family hind
  have hGeom := bernsteinInducedInertiaJacquetExclusion_of_supercuspidal.{uF, uV} i ν family
    hwhole' hsc
  exact bernsteinCategoryDecomposition_of_statementInputs.{uF, uV} i ν family hAssociate
    hdecomp hwhole hGeom

/-- Renard VI.7.2, all three conjuncts, from the same named inputs: the
split-subrepresentation conjunct follows from the decomposition and the
block-abelian conjunct is already proved. -/
theorem bernsteinDecompositionStatements_of_inputs
    (hAssociate :
      RepresentedParabolic.LeviSupercuspidalInductionAssociationStatement.{uF, max uF uV})
    (hind :
      RepresentedParabolic.LeviInductionNoSupercuspidalSubquotientStatement.{uF, max uF uV})
    (hdecomp : RationalCuspidalInertiaProductDecompositionStatement.{uF, max uF uV})
    (hwhole : RationalWholeCuspidalCategoryDecompositionStatement.{uF, uV})
    (hwhole' : RationalWholeCuspidalCategoryDecompositionStatement.{uF, max uF uV}) :
    BernsteinDecompositionStatements.{uF, uV} :=
  bernsteinDecompositionStatements_iff_decomposition.mpr
    (bernsteinDecompositionStatement_of_inputs hAssociate hind hdecomp hwhole hwhole')

set_option linter.defProp false in
/-- The reduction of Renard VI.7.2 to its named inputs, as a declaration whose
type is the implication. -/
def bernsteinDecompositionStatementsOfInputs :
    RepresentedParabolic.LeviSupercuspidalInductionAssociationStatement.{uF, max uF uV} →
    RepresentedParabolic.LeviInductionNoSupercuspidalSubquotientStatement.{uF, max uF uV} →
    RationalCuspidalInertiaProductDecompositionStatement.{uF, max uF uV} →
    RationalWholeCuspidalCategoryDecompositionStatement.{uF, uV} →
    RationalWholeCuspidalCategoryDecompositionStatement.{uF, max uF uV} →
      BernsteinDecompositionStatements.{uF, uV} :=
  bernsteinDecompositionStatements_of_inputs

end Langlands.CuspidalSupport
