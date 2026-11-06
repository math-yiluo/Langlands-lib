import Langlands.GroupScheme.IntegralModel.IntegralPointDescent
import Langlands.Geometry.Building.UnramifiedStabilizerDescent

/-! # The original model image under actual maximal-unramified base change -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

open Langlands.LocalGalois.Separable GaloisPointComparison
open Langlands.Geometry.Building

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  (M : IntegralModel ↥𝒪[F] F G)

local instance : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance : IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

/-- Base change of the supplied model to the actual integers in the separable
inertia fixed field, with its original generic identification transported. -/
def baseChangeUnramified : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
    (baseChanged F (inertiaFixedField F) G) :=
  M.baseChange (fixedFieldIntegers F) (inertiaFixedField F)

/-- The actual maximal-unramified integers meet the base field in its integers. -/
theorem unramifiedIntegerRange_intersection (x : F) :
    algebraMap F (inertiaFixedField F) x ∈
        Set.range (algebraMap (fixedFieldIntegers F) (inertiaFixedField F)) ↔
      x ∈ Set.range (algebraMap ↥𝒪[F] F) := by
  have range_iff (y : inertiaFixedField F) :
      y ∈ Set.range (algebraMap (fixedFieldIntegers F) (inertiaFixedField F)) ↔
        fixedFieldValuation F y ≤ 1 := by
    constructor
    · rintro ⟨a, rfl⟩
      exact a.property
    · intro hy
      exact ⟨⟨y, hy⟩, rfl⟩
  rw [range_iff, Valuation.HasExtension.val_map_le_one_iff
    (ValuativeRel.valuation F) (fixedFieldValuation F)]
  constructor
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨a, rfl⟩
    exact a.property

/-- Extension to the actual maximal-unramified field reflects the original image. -/
theorem mem_integralPoints_rationalExtend_iff_unramified (g : rationalPoints G) :
    rationalExtend F (inertiaFixedField F) G g ∈ M.baseChangeUnramified.integralPoints ↔
      g ∈ M.integralPoints :=
  M.mem_integralPoints_rationalExtend_iff (fixedFieldIntegers F) (inertiaFixedField F)
    unramifiedIntegerRange_intersection g

/-- The downstairs subgroup is the exact preimage of the extended original image. -/
theorem integralPoints_eq_comap_baseChangeUnramified :
    M.integralPoints = M.baseChangeUnramified.integralPoints.comap
      (rationalExtend F (inertiaFixedField F) G) :=
  M.integralPoints_eq_comap_baseChange (fixedFieldIntegers F) (inertiaFixedField F)
    unramifiedIntegerRange_intersection

/-- Actual scalar extension restricted to the two original-model image groups. -/
def unramifiedIntegralPointExtend :
    M.integralPoints →* M.baseChangeUnramified.integralPoints where
  toFun g := ⟨rationalExtend F (inertiaFixedField F) G g.val,
    (M.mem_integralPoints_rationalExtend_iff_unramified g.val).mpr g.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext (map_mul _ g.val h.val)

@[simp] theorem unramifiedIntegralPointExtend_coe (g : M.integralPoints) :
    (M.unramifiedIntegralPointExtend g :
      rationalPoints (baseChanged F (inertiaFixedField F) G)) =
        rationalExtend F (inertiaFixedField F) G g.val := rfl

variable [IsAffineHom G.X.hom]

private instance extensionAffineHom :
    IsAffineHom (baseChanged F (UnramifiedClosure F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (UnramifiedClosure F)))
  infer_instance

/-- An upstairs stabilizer comparison for the base change of this supplied model
 descends to its original image along a supplied injective equivariant embedding. -/
theorem integralPoints_eq_compactStabilizer_of_unramified
    (B : ValuationBuildingData G)
    (C : MaximalUnramified.BuildingData F (baseChanged F (UnramifiedClosure F) G))
    (e : B.ReducedBuilding → C.ReducedBuilding) (hinj : Function.Injective e)
    (he : ∀ (g : rationalPoints G) (z : B.ReducedBuilding),
      e (g • z) = rationalExtend F (UnramifiedClosure F) G g • e z)
    (z : B.ReducedBuilding)
    (hM : M.baseChangeUnramified.integralPoints = C.oneStabilizer (e z)) :
    M.integralPoints = B.compactStabilizer z := by
  rw [M.integralPoints_eq_comap_baseChangeUnramified, hM]
  exact MaximalUnramified.oneStabilizer_comap B C e hinj he z

end Langlands.GroupScheme.IntegralModel
