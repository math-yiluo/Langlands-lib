import Langlands.Geometry.Building.TorusUnitFixedPoint
import Langlands.Geometry.Building.SpecialTorusIntegralModelReduction
import Langlands.GroupScheme.IntegralModel.UnramifiedModelDescent
import Langlands.BruhatTits.IntegralModels.IntegralRootFiltration

/-! # Integral split tori from arbitrary subsets fixed by unramified units -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G H : GroupScheme (Spec (CommRingCat.of F))}
  {Y : Type v} [MulAction (rationalPoints (baseChanged F (inertiaFixedField F) G)) Y]

/-- If unramified units of a source group fix every point of a set, their images lie in
the character-kernel pointwise fixer. No apartment containing the set is required. -/
theorem map_characterValuationKernel_le_oneFixer_of_unitFixedSubset
    (i : H ⟶ G) (Z : Set Y)
    (hZ : ∀ y ∈ Z, IsFixedByUnramifiedTorusUnits F i y) :
    (characterValuationKernel (MaximalUnramified.valuation F)
      (baseChanged F (inertiaFixedField F) H)).map
        (rationalPoints.map
          ((GroupScheme.baseChange (baseMap F (inertiaFixedField F))).map i)) ≤
      characterValuationKernel (MaximalUnramified.valuation F)
          (baseChanged F (inertiaFixedField F) G) ⊓
        fixingSubgroup (rationalPoints (baseChanged F (inertiaFixedField F) G)) Z := by
  rintro _ ⟨s, hs, rfl⟩
  refine ⟨IntegerValuation.map_mem_characterValuationKernel
    (MaximalUnramified.valuation F) _ hs, ?_⟩
  exact (mem_fixingSubgroup_iff _).mpr fun y hy => hZ y hy s hs

local instance : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance : IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

open Langlands.BruhatTits.IntegralModels

variable {S : CommGroupScheme (Spec (CommRingCat.of F))}
  (iS : S.toGrp ⟶ G) (hS : IsSplitSubtorus iS)
  (M : IntegralModel ↥𝒪[F] F G)
  (Z : Set Y) (hZ : ∀ y ∈ Z, IsFixedByUnramifiedTorusUnits F iS y)
  (hM : characterValuationKernel (MaximalUnramified.valuation F)
      (baseChanged F (inertiaFixedField F) G) ⊓
      fixingSubgroup (rationalPoints (baseChanged F (inertiaFixedField F) G)) Z ≤
    M.baseChangeUnramified.integralPoints)

include hS hZ hM

/-- A supplied model containing the character-kernel fixer of a unit-fixed subset contains
a closed integral split torus with the prescribed generic fibre. -/
theorem exists_closedIntegralSplitTorus_of_unitFixedSubset :
    ∃ A : IntegralSplitTorusData M iS, IsClosedSubgroup A.inclusion := by
  have : Infinite (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    SpecialTorusIntegralModel.infinite_residueField_fixedFieldIntegers F
  obtain ⟨𝒮, j, e, h𝒮, hj, hgen⟩ :=
    IntegralModel.SplitTorusClosure.exists_isSplitTorus_genericTorusMap_eq_of_baseChange
      M (fixedFieldIntegers F) (inertiaFixedField F) (MaximalUnramified.valuation F)
      (SpecialTorusIntegralModel.valuation_units_eq_one F)
      (fun x hx => (IntegralModel.unramifiedIntegerRange_intersection x).mp hx)
      iS hS.1 hS.2
      ((map_characterValuationKernel_le_oneFixer_of_unitFixedSubset iS Z hZ).trans hM)
  exact ⟨
    { torus := 𝒮
      isSplit := h𝒮
      inclusion := j
      genericIso := e
      generic_comm := hgen }, hj⟩

/-- A chosen actual closed integral split torus in the supplied model. Its generic fibre
and inclusion square are those required by `IntegralSplitTorusData M iS`. -/
def integralSplitTorusOfUnitFixedSubset : IntegralSplitTorusData M iS :=
  Classical.choose
    (exists_closedIntegralSplitTorus_of_unitFixedSubset iS hS M Z hZ hM)

/-- The chosen integral inclusion is a closed immersion. -/
theorem integralSplitTorusOfUnitFixedSubset_isClosedSubgroup :
    IsClosedSubgroup (integralSplitTorusOfUnitFixedSubset iS hS M Z hZ hM).inclusion :=
  Classical.choose_spec
    (exists_closedIntegralSplitTorus_of_unitFixedSubset iS hS M Z hZ hM)

end Langlands.Geometry.Building
