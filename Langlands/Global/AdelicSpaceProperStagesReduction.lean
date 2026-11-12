import Langlands.Global.AdelicSpaceProperInputsStatement
import Langlands.Global.AdelicSpaceStageProperReduction
import Langlands.Global.AdelicSpaceStagePreimageReduction

/-! # Reduction of proper adelic stages to three geometric inputs -/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry (AlgebraicSpace)
open Langlands.AlgebraicGeometry.AlgebraicSpace

namespace Langlands.Global

/-- The conditional reduction of the unchanged proper-stage target to three
geometric inputs, all in the same arbitrary universe. -/
def AdelicSpaceProperStagesReductionStatement : Prop :=
  LocalFieldProperPointMapStatement.{u} →
    SpaceValuativeExistenceStatement.{u} →
      ProperSchemeBaseChangeStatement.{u} →
        AdelicSpaceProperStagesStatement.{u}

/-- The curve-place proper-stage statement follows from local properness, valuative
existence and preservation of properness under a change of base scheme. -/
theorem curvePlaceSpaceProperStages_of_inputs
    (hlocal : LocalFieldProperPointMapStatement.{u})
    (hv : SpaceValuativeExistenceStatement.{u})
    (hbc : ProperSchemeBaseChangeStatement.{u}) :
    CurvePlaceSpaceProperStagesStatement.{u} := by
  intro k F _ _ _ _ _ _ _ S hS X Y hX hftX hY hftY f hf T
  exact ⟨curvePlaceSpaceStage_isProperMap_of_proper k F S
      hlocal hbc hS hX hftX hY hftY f hf T,
    curvePlaceSpaceStagePreimage_of_valuative k F S hv hS hX hftX f T
      (hbc _ _ _ _ _ _ hf)⟩

/-- The number-field proper-stage statement follows from the same three inputs,
with every infinite-place factor retained. -/
theorem numberFieldSpaceProperStages_of_inputs
    (hlocal : LocalFieldProperPointMapStatement.{u})
    (hv : SpaceValuativeExistenceStatement.{u})
    (hbc : ProperSchemeBaseChangeStatement.{u}) :
    NumberFieldSpaceProperStagesStatement.{u} := by
  intro K _ _ S X Y hX hftX hY hftY f hf T
  exact ⟨numberFieldSpaceStage_isProperMap_of_proper K S
      hlocal hbc hX hftX hY hftY f hf T,
    numberFieldSpaceStagePreimage_of_valuative K S hv hX hftX f T
      (hbc _ _ _ _ _ _ hf)⟩

/-- The unchanged two-characteristic target reduces to the three explicit geometric inputs. -/
theorem adelicSpaceProperStages_of_inputs
    (hlocal : LocalFieldProperPointMapStatement.{u})
    (hv : SpaceValuativeExistenceStatement.{u})
    (hbc : ProperSchemeBaseChangeStatement.{u}) :
    AdelicSpaceProperStagesStatement.{u} :=
  ⟨curvePlaceSpaceProperStages_of_inputs hlocal hv hbc,
    numberFieldSpaceProperStages_of_inputs hlocal hv hbc⟩

/-- The implemented conditional reduction. -/
theorem adelicSpaceProperStagesReduction :
    AdelicSpaceProperStagesReductionStatement.{u} :=
  adelicSpaceProperStages_of_inputs

end Langlands.Global
