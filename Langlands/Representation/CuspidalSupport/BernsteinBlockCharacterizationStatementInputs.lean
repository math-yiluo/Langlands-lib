import Langlands.Representation.CuspidalSupport.BernsteinFixedLeviEmbeddingReduction
import Langlands.Representation.CuspidalSupport.BernsteinLeviInertiaProjection
import Langlands.Representation.CuspidalSupport.BernsteinDecompositionInputsAssembly
import Langlands.Representation.CuspidalSupport.BernsteinInducedInertiaGeometricExclusion

/-! # Renard VI.7.2 Proposition from five named statements

The characterization of a Bernstein block (Renard VI.7.2, Proposition) follows from
five published statements: VI.3.3.1 (`RationalCuspidalInertiaDecompositionStatement`),
VI.3.5 (`RationalWholeCuspidalCategoryDecompositionStatement`), represented VI.5.2
(`RepresentedParabolic.LeviInductionNoSupercuspidalSubquotientStatement`), VI.10.3
(`BernsteinBlockJacquetFaithfulStatement`) and VI.4.1
(`RationalSummandSmallProgeneratorStatement`). This module only composes published
reductions. None of the five statements is proved here; each remains an explicit
hypothesis. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme

namespace Langlands.CuspidalSupport

universe uF uV

/-- The per-family inputs of `bernsteinBlockCharacterization_of_leviInputs` (the Levi block
projection and the geometric Jacquet exclusion) follow from Renard VI.3.3.1, VI.3.5 and
represented VI.5.2. -/
theorem bernsteinBlockCharacterizationLeviInputs_of_statements
    (hSplit : RationalCuspidalInertiaDecompositionStatement.{uF, max uF uV})
    (hwhole : RationalWholeCuspidalCategoryDecompositionStatement.{uF, max uF uV})
    (hind : RepresentedParabolic.LeviInductionNoSupercuspidalSubquotientStatement.{uF,
      max uF uV}) :
    BernsteinBlockCharacterizationLeviInputs.{uF, uV} := by
  intro F _ _ _ _ G _ _ T i ν _ _ family
  exact ⟨bernsteinLeviBlockProjectionOfRationalInertiaDecomposition.{uF, uV} i ν family hSplit,
    bernsteinInducedInertiaJacquetExclusion_of_supercuspidal.{uF, uV} i ν family hwhole
      (bernsteinJacquetExclusionOfInertiaBlockSupercuspidal.{uF, uV} i ν family hind)⟩

/-- Renard VI.7.2, Proposition (characterizations of a Bernstein block), conditional on
five named statements: VI.3.3.1, VI.3.5, represented VI.5.2, VI.10.3 and VI.4.1. -/
theorem bernsteinBlockCharacterization_of_statements
    (hSplit : RationalCuspidalInertiaDecompositionStatement.{uF, max uF uV})
    (hwhole : RationalWholeCuspidalCategoryDecompositionStatement.{uF, max uF uV})
    (hind : RepresentedParabolic.LeviInductionNoSupercuspidalSubquotientStatement.{uF,
      max uF uV})
    (hJF : BernsteinBlockJacquetFaithfulStatement.{uF, uV})
    (hProg : RationalSummandSmallProgeneratorStatement.{uF, max uF uV}) :
    BernsteinBlockCharacterizationStatement.{uF, uV} :=
  bernsteinBlockCharacterization_of_leviInputs.{uF, uV}
    (bernsteinBlockCharacterizationLeviInputs_of_statements.{uF, uV} hSplit hwhole hind)
    hJF hProg

set_option linter.defProp false in
/-- The reduction of Renard VI.7.2 Proposition to VI.3.3.1, VI.3.5, represented VI.5.2,
VI.10.3 and VI.4.1, as a declaration whose type is the implication. -/
def bernsteinBlockCharacterizationOfStatements :
    RationalCuspidalInertiaDecompositionStatement.{uF, max uF uV} →
      RationalWholeCuspidalCategoryDecompositionStatement.{uF, max uF uV} →
      RepresentedParabolic.LeviInductionNoSupercuspidalSubquotientStatement.{uF, max uF uV} →
      BernsteinBlockJacquetFaithfulStatement.{uF, uV} →
      RationalSummandSmallProgeneratorStatement.{uF, max uF uV} →
      BernsteinBlockCharacterizationStatement.{uF, uV} :=
  bernsteinBlockCharacterization_of_statements.{uF, uV}

end Langlands.CuspidalSupport
