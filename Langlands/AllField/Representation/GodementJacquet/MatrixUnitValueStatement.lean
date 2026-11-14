import Langlands.Representation.GodementJacquet.MatrixUnitValueStatement
import Langlands.AllField.Representation.GodementJacquet.AnalyticData
/-! # The unit is an actual matrix rational value -/

noncomputable section

namespace Langlands.AllField.GodementJacquet
open Langlands.GodementJacquet hiding MatrixUnitValueStatement
open Langlands.AllField.GodementJacquet

open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

universe uF uV

/-- Every nonzero smooth representation has actual matrix rational value `1`,
on both the original and inverse-transpose sides. -/
def MatrixUnitValueStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F],
    ∀ n : ℕ,
      letI : MeasurableSpace (Langlands.GeneralLinear (n + 1) F) := borel _
      letI : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
      ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V] [Nontrivial V]
        (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V),
        IsSmooth σ →
        (1 : RationalFunctions) ∈ Langlands.AllField.GodementJacquet.Padic.matrixRationalValues F σ ∧
          (1 : RationalFunctions) ∈ Langlands.AllField.GodementJacquet.Padic.iotaMatrixRationalValues F σ

end Langlands.AllField.GodementJacquet
