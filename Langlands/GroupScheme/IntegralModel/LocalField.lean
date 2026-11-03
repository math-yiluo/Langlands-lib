import Langlands.GroupScheme.IntegralModelReduction
import Mathlib.NumberTheory.LocalField.Basic

/-! # Integral models over the actual integers of a nonarchimedean local field -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Integral models over the actual valuation integer ring, with generic field `F`. -/
abbrev LocalFieldIntegralModel (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (G : GroupScheme (Spec (CommRingCat.of F))) :=
  IntegralModel ↥𝒪[F] F G

namespace LocalFieldIntegralModel

section Coefficients

variable (F : Type u) [Field F] [ValuativeRel F]

/-- The fraction-field map is the actual subtype inclusion of the valuation ring. -/
abbrev integerInclusion : ↥𝒪[F] →+* F := (ValuativeRel.valuation F).integer.subtype

/-- The quotient to the actual residue field of the valuation ring. -/
abbrev residueHom : ↥𝒪[F] →+* 𝓀[F] := IsLocalRing.residue ↥𝒪[F]

@[simp] theorem integerInclusion_apply (x : ↥𝒪[F]) :
    integerInclusion F x = (x : F) := rfl

/-- The canonical algebra structure uses the actual valuation-ring inclusion. -/
theorem integerInclusion_eq_algebraMap : integerInclusion F = algebraMap ↥𝒪[F] F := rfl

/-- The generic-base morphism is induced by the actual valuation-ring inclusion. -/
theorem genericBase_eq :
    Spec.algebraMap ↥𝒪[F] F = Spec.map (CommRingCat.ofHom (integerInclusion F)) := rfl

/-- The special-base morphism is induced by the actual residue quotient. -/
theorem residueBase_eq :
    IntegralModel.residueBaseMap ↥𝒪[F] = Spec.map (CommRingCat.ofHom (residueHom F)) := rfl

end Coefficients

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} (M : LocalFieldIntegralModel F G)

/-- Integral sections are points over the actual valuation integer ring. -/
abbrev integralSections : Type u := IntegralModel.integralSections M

/-- The original integral-point map, specialized to the actual integer-ring inclusion. -/
abbrev integralPointMap : M.integralSections →* rationalPoints G :=
  IntegralModel.integralPointMap M

/-- The actual local-field generic-point evaluation formula. -/
theorem integralPointMap_left (x : M.integralSections) :
    (M.integralPointMap x).left =
      pullback.lift (Spec.map (CommRingCat.ofHom (integerInclusion F)) ≫ x.left) (𝟙 _)
        (by simp [← genericBase_eq, Category.assoc, x.w]) ≫ M.genericIso.hom.hom.hom.left :=
  IntegralModel.integralPointMap_left M x

/-- The same integral-point subgroup in the existing `F`-rational-point group. -/
abbrev integralPoints : Subgroup (rationalPoints G) := IntegralModel.integralPoints M

/-- The full special-fibre group scheme over the actual residue field `𝓀[F]`. -/
abbrev specialFibre : GroupScheme (Spec (CommRingCat.of 𝓀[F])) :=
  IntegralModel.specialFibre M

/-- Reduction uses the actual quotient from the valuation ring to its residue field. -/
abbrev reduction : M.integralSections →* rationalPoints M.specialFibre :=
  IntegralModel.reduction M

/-- The actual local-field reduction evaluation formula. -/
theorem reduction_left (x : M.integralSections) :
    (M.reduction x).left =
      pullback.lift (Spec.map (CommRingCat.ofHom (residueHom F)) ≫ x.left) (𝟙 _)
        (by simp [← residueBase_eq, Category.assoc, x.w]) :=
  IntegralModel.reduction_left M x

/-- The same congruence kernel in the group of integral sections. -/
abbrev congruenceKernel : Subgroup M.integralSections := IntegralModel.congruenceKernel M

/-- The congruence image inside the existing `F`-rational-point group. -/
abbrev congruenceSubgroup : Subgroup (rationalPoints G) := IntegralModel.congruenceSubgroup M

/-- The congruence image is normal in the integral-point image. -/
theorem congruenceSubgroup_normal_in_integralPoints :
    (M.congruenceSubgroup.subgroupOf M.integralPoints).Normal :=
  IntegralModel.congruenceSubgroup_normal_in_integralPoints M

end LocalFieldIntegralModel
end Langlands.GroupScheme
