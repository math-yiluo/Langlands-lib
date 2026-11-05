import Langlands.Global.AdelicUnimodularityStatement
import Langlands.Global.AdelicNormOneModularCharacter
import Langlands.Global.AdelicLocalModularComparison
import Langlands.GroupScheme.Lie.AdjointDeterminantReductiveStatement

/-! # Reduction of actual adelic Haar unimodularity to local and algebraic inputs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Global.AdelicGroupPoints

/-- The exact local analytic and reductive algebraic inputs suffice for the
existing universal Haar-unimodularity conjunction. -/
def AdelicHaarUnimodularityReductionStatement : Prop :=
  PlaceGroupPoints.LocalModularCharacterAdjointDeterminantStatement.{u} →
    Langlands.GroupScheme.Lie.ConnectedReductiveAdjointDeterminantStatement.{u} →
      AdelicHaarUnimodularityStatement.{u}

/-- The analytic adjoint comparison supplies the full norm-one Haar assertion. -/
theorem normOneHaarRightInvariantStatement_of_modularComparison
    (hcompare : AdelicModularCharacterAdjointDeterminantStatement.{u}) :
    NormOneHaarRightInvariantStatement.{u} := by
  intro F _ _ G _ _ hsm hc
  exact normOneHaarRightInvariant_of_characterNorm F G
    (Langlands.GroupScheme.Lie.adjointDeterminantCharacter G).toMul
    (hcompare F G hsm hc)

/-- Analytic comparison and reductive determinant triviality supply the full
connected reductive Haar assertion. -/
theorem connectedReductiveHaarRightInvariantStatement_of_modularComparison
    (hcompare : AdelicModularCharacterAdjointDeterminantStatement.{u})
    (hdet : Langlands.GroupScheme.Lie.ConnectedReductiveAdjointDeterminantStatement.{u}) :
    ConnectedReductiveHaarRightInvariantStatement.{u} := by
  intro F _ _ G _ _ hG
  exact haarRightInvariant_of_adjointDeterminant_eq_zero F G
    (hcompare F G hG.smooth hG.connectedSpace) (hdet F G hG)

/-- The two independently specified analytic and algebraic inputs imply the
existing exact conjunction for the original fixed Haar measures. -/
theorem adelicHaarUnimodularityStatement_of_modularComparison
    (hcompare : AdelicModularCharacterAdjointDeterminantStatement.{u})
    (hdet : Langlands.GroupScheme.Lie.ConnectedReductiveAdjointDeterminantStatement.{u}) :
    AdelicHaarUnimodularityStatement.{u} :=
  ⟨normOneHaarRightInvariantStatement_of_modularComparison hcompare,
    connectedReductiveHaarRightInvariantStatement_of_modularComparison hcompare hdet⟩

/-- The all-place local comparison already implies the norm-one part, including
smooth connected groups that are not reductive. -/
theorem normOneHaarRightInvariantStatement_of_local
    (hlocal : PlaceGroupPoints.LocalModularCharacterAdjointDeterminantStatement.{u}) :
    NormOneHaarRightInvariantStatement.{u} :=
  normOneHaarRightInvariantStatement_of_modularComparison
    (adelicModularCharacterAdjointDeterminantStatement_of_local hlocal)

/-- Local analytic comparison and reductive determinant triviality imply both
assertions at the same arbitrary universe. -/
theorem adelicHaarUnimodularityStatement_of_local
    (hlocal : PlaceGroupPoints.LocalModularCharacterAdjointDeterminantStatement.{u})
    (hdet : Langlands.GroupScheme.Lie.ConnectedReductiveAdjointDeterminantStatement.{u}) :
    AdelicHaarUnimodularityStatement.{u} :=
  adelicHaarUnimodularityStatement_of_modularComparison
    (adelicModularCharacterAdjointDeterminantStatement_of_local hlocal) hdet

/-- The existing central-times-derived structural statement is sufficient for
the remaining algebraic input, once the local analytic statement is proved. -/
theorem adelicHaarUnimodularityStatement_of_local_and_centralDerivedProduct
    (hlocal : PlaceGroupPoints.LocalModularCharacterAdjointDeterminantStatement.{u})
    (hprod : Langlands.GroupScheme.ReductiveCentralDerivedProductStatement.{u}) :
    AdelicHaarUnimodularityStatement.{u} :=
  adelicHaarUnimodularityStatement_of_local hlocal
    (Langlands.GroupScheme.Lie.connectedReductiveAdjointDeterminant_of_centralDerivedProduct
      hprod)

/-- Proof of the named conditional reduction. -/
theorem adelicHaarUnimodularityReduction :
    AdelicHaarUnimodularityReductionStatement.{u} :=
  adelicHaarUnimodularityStatement_of_local

end Langlands.Global.AdelicGroupPoints
