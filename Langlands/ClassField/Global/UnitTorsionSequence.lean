import Langlands.ClassField.Global.FullLogQuotientAction
import Langlands.ClassField.Global.LocalUnitCohomology

/-! # The finite torsion exact sequence of actual arithmetic units -/

noncomputable section

open NumberField CategoryTheory
open scoped Classical

attribute [local instance] Units.mulDistribMulActionRight

namespace Langlands.ClassField.Global

universe u v

variable (F : Type u) [Field F] (E : Type v) [Field E] [Algebra F E]

/-- Arithmetic automorphisms preserve the torsion subgroup of ordinary units. -/
theorem unit_smul_mem_torsion (g : E ≃ₐ[F] E) {x : (𝓞 E)ˣ}
    (hx : x ∈ NumberField.Units.torsion E) : g • x ∈ NumberField.Units.torsion E := by
  change IsOfFinOrder (g • x)
  exact (MulDistribMulAction.toMulAut (E ≃ₐ[F] E) (𝓞 E)ˣ g).toMonoidHom.isOfFinOrder hx

/-- Restrict the actual arithmetic unit automorphisms to their torsion subgroup. -/
def unitTorsionAut : (E ≃ₐ[F] E) →* MulAut (NumberField.Units.torsion E) where
  toFun g :=
    { toFun x := ⟨g • (x : (𝓞 E)ˣ), unit_smul_mem_torsion F E g x.2⟩
      invFun x := ⟨g⁻¹ • (x : (𝓞 E)ˣ), unit_smul_mem_torsion F E g⁻¹ x.2⟩
      left_inv _ := Subtype.ext (inv_smul_smul g _)
      right_inv _ := Subtype.ext (smul_inv_smul g _)
      map_mul' x y := Subtype.ext (smul_mul' g (x : (𝓞 E)ˣ) y) }
  map_one' := MulEquiv.ext fun x => Subtype.ext (one_smul _ (x : (𝓞 E)ˣ))
  map_mul' g h := MulEquiv.ext fun x => Subtype.ext (mul_smul g h (x : (𝓞 E)ˣ))

@[simp] theorem unitTorsionAut_coe (g : E ≃ₐ[F] E) (x : NumberField.Units.torsion E) :
    (unitTorsionAut F E g x : (𝓞 E)ˣ) = g • (x : (𝓞 E)ˣ) := rfl

/-- The restricted torsion action, installed explicitly. -/
@[instance_reducible]
def unitTorsionAction : MulDistribMulAction (E ≃ₐ[F] E) (NumberField.Units.torsion E) where
  __ := MulAction.compHom _ (unitTorsionAut F E)
  smul_one g := map_one (unitTorsionAut F E g)
  smul_mul g x y := map_mul (unitTorsionAut F E g) x y

attribute [local instance] unitTorsionAction unitsModuloTorsionAction

/-- The actual ring-integer units with their arithmetic action over lifted integers. -/
abbrev ringIntegerUnitsRepresentation :
    Rep.{v} NormalizedTwoCocycle.CoefficientScalars.{v} (E ≃ₐ[F] E) :=
  NormalizedTwoCocycle.coefficientRepresentation (E ≃ₐ[F] E) (𝓞 E)ˣ

/-- The actual unit torsion subgroup with the restricted arithmetic action. -/
abbrev unitTorsionRepresentation :
    Rep.{v} NormalizedTwoCocycle.CoefficientScalars.{v} (E ≃ₐ[F] E) :=
  NormalizedTwoCocycle.coefficientRepresentation (E ≃ₐ[F] E) (NumberField.Units.torsion E)

@[simp] theorem ringIntegerUnitsRepresentation_apply (g : E ≃ₐ[F] E)
    (x : Additive (𝓞 E)ˣ) :
    (ringIntegerUnitsRepresentation F E).ρ g x = Additive.ofMul (g • x.toMul) := rfl

@[simp] theorem unitTorsionRepresentation_apply (g : E ≃ₐ[F] E)
    (x : Additive (NumberField.Units.torsion E)) :
    (unitTorsionRepresentation F E).ρ g x =
      Additive.ofMul (unitTorsionAut F E g x.toMul) := rfl

/-- The inclusion of the torsion units as a morphism of arithmetic representations. -/
def unitTorsionInclusion : unitTorsionRepresentation F E ⟶ ringIntegerUnitsRepresentation F E :=
  Rep.ofHom
    { toLinearMap :=
        { toFun x := Additive.ofMul ((@Additive.toMul (NumberField.Units.torsion E) x : NumberField.Units.torsion E) : (𝓞 E)ˣ)
          map_add' _ _ := rfl
          map_smul' _ _ := rfl }
      isIntertwining' _ := rfl }

/-- The actual quotient of units by torsion as a morphism of representations. -/
def unitsModuloTorsionProjection :
    ringIntegerUnitsRepresentation F E ⟶ unitsModuloTorsionRepresentation F E :=
  Rep.ofHom
    { toLinearMap :=
        { toFun x := Additive.ofMul (QuotientGroup.mk (@Additive.toMul (𝓞 E)ˣ x))
          map_add' x y := congrArg Additive.ofMul
            (map_mul (QuotientGroup.mk' (NumberField.Units.torsion E)) (@Additive.toMul (𝓞 E)ˣ x) (@Additive.toMul (𝓞 E)ˣ y))
          map_smul' r x := congrArg Additive.ofMul
            (map_zpow (QuotientGroup.mk' (NumberField.Units.torsion E)) (@Additive.toMul (𝓞 E)ˣ x) r.down) }
      isIntertwining' g := by
        apply LinearMap.ext
        intro x
        rfl }

@[simp] theorem unitTorsionInclusion_apply (x : Additive (NumberField.Units.torsion E)) :
    (unitTorsionInclusion F E).hom x = Additive.ofMul (x.toMul : (𝓞 E)ˣ) := rfl

@[simp] theorem unitsModuloTorsionProjection_apply (x : Additive (𝓞 E)ˣ) :
    (unitsModuloTorsionProjection F E).hom x =
      Additive.ofMul (QuotientGroup.mk x.toMul) := rfl

/-- The short complex from torsion units to ordinary units and their torsion quotient. -/
def unitTorsionSequence :
    ShortComplex (Rep.{v} NormalizedTwoCocycle.CoefficientScalars.{v} (E ≃ₐ[F] E)) :=
  ShortComplex.mk (unitTorsionInclusion F E) (unitsModuloTorsionProjection F E) (by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact congrArg Additive.ofMul ((QuotientGroup.eq_one_iff
      ((@Additive.toMul (NumberField.Units.torsion E) x : NumberField.Units.torsion E) : (𝓞 E)ˣ)).2
      (@Additive.toMul (NumberField.Units.torsion E) x).property))

/-- The arithmetic torsion sequence is short exact. -/
theorem unitTorsionSequence_shortExact : (unitTorsionSequence F E).ShortExact := by
  refine repShortExact_of_values _ ?_ ?_ ?_
  · intro a b h
    have h' : ((@Additive.toMul (NumberField.Units.torsion E) a : NumberField.Units.torsion E) : (𝓞 E)ˣ) =
        ((@Additive.toMul (NumberField.Units.torsion E) b : NumberField.Units.torsion E) : (𝓞 E)ˣ) := h
    exact congrArg Additive.ofMul (Subtype.ext h')
  · intro x hx
    have hx' : QuotientGroup.mk (@Additive.toMul (𝓞 E)ˣ x) =
        (1 : (𝓞 E)ˣ ⧸ NumberField.Units.torsion E) := hx
    exact ⟨Additive.ofMul (⟨@Additive.toMul (𝓞 E)ˣ x, (QuotientGroup.eq_one_iff _).1 hx'⟩ :
      NumberField.Units.torsion E), rfl⟩
  · intro q
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (@Additive.toMul ((𝓞 E)ˣ ⧸ NumberField.Units.torsion E) q)
    exact ⟨Additive.ofMul x, congrArg Additive.ofMul hx⟩

/-- For a number field the actual torsion coefficient module is finite. -/
theorem unitTorsionRepresentation_finite [NumberField E] :
    Finite (unitTorsionRepresentation F E).V := by
  change Finite (Additive (NumberField.Units.torsion E))
  infer_instance

end Langlands.ClassField.Global
