import Langlands.Geometry.Building.SpecialTorusBoundedModelStatement
import Langlands.Geometry.Building.SpecialTorusIntegralModelStatement
import Langlands.Geometry.Building.FullValidity.DatumTransport.Base
import Langlands.Geometry.Building.RegularUnitExistence
import Langlands.GroupScheme.IntegralModel.SplitTorusBoundedPoints
import Langlands.GroupScheme.IntegralModel.SpecialTorusNeutralModel

/-! # The special-torus model from a model containing bounded torus points -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

namespace SpecialTorusIntegralModel

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- The residue field of the integers of the maximal unramified extension is infinite: it is
an algebraic closure of the residue field of `F`. -/
theorem infinite_residueField_fixedFieldIntegers :
    Infinite (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
  MaximalUnramified.valuationSubring_eq F ▸ MaximalUnramified.infinite_residueField F

/-- The normalized valuation of the maximal unramified extension is one on the units of its
integers. -/
theorem valuation_units_eq_one (a : (fixedFieldIntegers F)ˣ) :
    MaximalUnramified.valuation F
        (algebraMap (fixedFieldIntegers F) (inertiaFixedField F) (a : fixedFieldIntegers F)) =
      1 :=
  Valuation.Integers.one_of_isUnit' a.isUnit fun x =>
    (Valuation.mem_valuationSubring_iff _ _).mp
      ((MaximalUnramified.mem_valuationSubring_iff F x).mpr x.property)

end SpecialTorusIntegralModel

section Reduction

open SpecialTorusIntegralModel

local instance specialTorusReductionAlgebra {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance specialTorusReductionIsScalarTower {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

/-- **Reduction of the special-torus model to bounded torus points.** The smooth integral
model with special-torus data (`SpecialTorusIntegralModelStatement`) follows from a smooth
model containing the maximal bounded subgroups of `S` and of a maximal `K`-split torus over
the maximal-unramified integers (`SpecialTorusBoundedModelStatement`). -/
theorem specialTorusIntegralModelStatement_of_boundedModel
    (h : SpecialTorusBoundedModelStatement.{u}) : SpecialTorusIntegralModelStatement.{u} := by
  intro F _ _ _ _ G hG S iS hS
  obtain ⟨M, hM, hSb, A, iA, hA, hAb⟩ := h F G hG S iS hS
  have : Infinite (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    infinite_residueField_fixedFieldIntegers F
  have : IsDiscreteValuationRing (fixedFieldIntegers F) :=
    fixedFieldIntegersIsDVR_of_valuesFromBase F (fixedFieldValuesFromBase F)
  refine IntegralModel.exists_connected_specialTorusModel hG S iS M hM ?_ ?_
  · exact IntegralModel.SplitTorusClosure.exists_isSplitTorus_genericTorusMap_eq_of_baseChange
      M (fixedFieldIntegers F) (inertiaFixedField F) (MaximalUnramified.valuation F)
      (valuation_units_eq_one F)
      (fun x hx => (IntegralModel.unramifiedIntegerRange_intersection x).mp hx)
      iS hS.1.1 hS.1.2 hSb
  · obtain ⟨𝒜, a, e, h𝒜, ha, hgen⟩ :=
      IntegralModel.SplitTorusClosure.exists_isSplitTorus_genericTorusMap_eq_of_bounded
        M.baseChangeUnramified (MaximalUnramified.valuation F) (valuation_units_eq_one F)
        iA hA.1.1 hA.1.2 hAb
    refine ⟨𝒜, a, h𝒜, ha, ?_⟩
    rw [hgen]
    exact DatumTransport.isMaximalSplitTorus_torusIso_comp hA e

end Reduction

/-- **The special-torus model reduces to bounded torus points** (statement). A smooth model
containing the maximal bounded subgroups of a maximal `F`-split torus `S` and of a maximal
`K`-split torus over the maximal-unramified integers (`SpecialTorusBoundedModelStatement`)
yields the smooth integral model with special-torus data of KP Proposition 9.3.4
(`SpecialTorusIntegralModelStatement`). -/
def SpecialTorusIntegralModelReductionStatement : Prop :=
  SpecialTorusBoundedModelStatement.{u} → SpecialTorusIntegralModelStatement.{u}

/-- The reduction statement holds. -/
theorem specialTorusIntegralModelReductionStatement :
    SpecialTorusIntegralModelReductionStatement.{u} :=
  specialTorusIntegralModelStatement_of_boundedModel

end Langlands.Geometry.Building
