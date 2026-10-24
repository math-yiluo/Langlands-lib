import Langlands.ClassField.Global.FullLogIntegralSplitting
import Langlands.GroupTheory.CocycleCohomology
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-! # Units modulo torsion and the logarithmic lattice as arithmetic representations -/

noncomputable section

open NumberField CategoryTheory
open scoped Classical

attribute [local instance] Units.mulDistribMulActionRight

namespace Langlands.ClassField.Global

universe u v

variable (F : Type u) [Field F] (E : Type v) [Field E] [NumberField E] [Algebra F E]

/-- The actual unit automorphisms descend to units modulo their torsion subgroup. -/
def unitsModuloTorsionAut : (E ≃ₐ[F] E) →*
    (((𝓞 E)ˣ ⧸ NumberField.Units.torsion E) ≃*
      ((𝓞 E)ˣ ⧸ NumberField.Units.torsion E)) where
  toFun g := QuotientGroup.congr (NumberField.Units.torsion E)
    (NumberField.Units.torsion E)
    (MulDistribMulAction.toMulAut (E ≃ₐ[F] E) (𝓞 E)ˣ g)
    (MulEquiv.map_torsion _)
  map_one' := by
    apply MulEquiv.ext
    intro q
    induction q using QuotientGroup.induction_on with
    | H x => change QuotientGroup.mk ((1 : E ≃ₐ[F] E) • x) = QuotientGroup.mk x; simp
  map_mul' g h := by
    apply MulEquiv.ext
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      change QuotientGroup.mk ((g * h) • x) = QuotientGroup.mk (g • h • x)
      rw [mul_smul]

omit [NumberField E] in
@[simp] theorem unitsModuloTorsionAut_mk (g : E ≃ₐ[F] E) (x : (𝓞 E)ˣ) :
    unitsModuloTorsionAut F E g (QuotientGroup.mk x) = QuotientGroup.mk (g • x) := rfl

/-- The natural quotient action, installed explicitly. -/
@[instance_reducible]
def unitsModuloTorsionAction :
    MulDistribMulAction (E ≃ₐ[F] E) ((𝓞 E)ˣ ⧸ NumberField.Units.torsion E) where
  __ := MulAction.compHom _ (unitsModuloTorsionAut F E)
  smul_one g := map_one (unitsModuloTorsionAut F E g)
  smul_mul g x y := map_mul (unitsModuloTorsionAut F E g) x y

attribute [local instance] unitsModuloTorsionAction

local instance : AddCommGroup (Additive ((𝓞 E)ˣ ⧸ NumberField.Units.torsion E)) :=
  inferInstance

/-- The full logarithm equivalence carries the natural quotient action to the lattice action. -/
theorem fullLogEmbeddingEquiv_equivariant (g : E ≃ₐ[F] E)
    (x : Additive ((𝓞 E)ˣ ⧸ NumberField.Units.torsion E)) :
    fullLogEmbeddingEquiv E (Additive.ofMul (unitsModuloTorsionAut F E g x.toMul)) =
      fullLogUnitLatticeAut F E g (fullLogEmbeddingEquiv E x) := by
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective x.toMul
  have hx : x = Additive.ofMul (QuotientGroup.mk y) := congrArg Additive.ofMul hy.symm
  subst x
  apply Subtype.ext
  simpa only [toMul_ofMul, unitsModuloTorsionAut_mk,
    fullLogEmbeddingEquiv_apply, fullLogUnitLatticeAut_apply] using
      fullLogEmbeddingToHyperplane_equivariant F E g y

/-- Ordinary quotient-unit coefficients, with the natural arithmetic action. -/
abbrev unitsModuloTorsionRepresentation :
    Rep.{v} NormalizedTwoCocycle.CoefficientScalars.{v} (E ≃ₐ[F] E) :=
  NormalizedTwoCocycle.coefficientRepresentation (E ≃ₐ[F] E)
    ((𝓞 E)ˣ ⧸ NumberField.Units.torsion E)

omit [NumberField E] in
@[simp] theorem unitsModuloTorsionRepresentation_apply (g : E ≃ₐ[F] E)
    (x : Additive ((𝓞 E)ˣ ⧸ NumberField.Units.torsion E)) :
    (unitsModuloTorsionRepresentation F E).ρ g x =
      Additive.ofMul (unitsModuloTorsionAut F E g x.toMul) := rfl

/-- The actual full logarithmic lattice with its restricted arithmetic action. -/
def fullLogUnitLatticeRepresentation :
    Rep.{v} NormalizedTwoCocycle.CoefficientScalars.{v} (E ≃ₐ[F] E) :=
  Rep.of
    { toFun g := (fullLogUnitLatticeAut F E g).toLinearMap.restrictScalars
        NormalizedTwoCocycle.CoefficientScalars.{v}
      map_one' := by ext x; simp
      map_mul' g h := by ext x; simp }

@[simp] theorem fullLogUnitLatticeRepresentation_apply (g : E ≃ₐ[F] E)
    (x : fullLogUnitLattice E) :
    (fullLogUnitLatticeRepresentation F E).ρ g x = fullLogUnitLatticeAut F E g x := rfl

/-- The full logarithm gives an isomorphism of the actual arithmetic representations. -/
def fullLogEmbeddingRepresentationIso :
    unitsModuloTorsionRepresentation F E ≅ fullLogUnitLatticeRepresentation F E :=
  Rep.mkIso (.mk ((fullLogEmbeddingEquiv E).restrictScalars
    NormalizedTwoCocycle.CoefficientScalars.{v}) (fun g => by
      apply LinearMap.ext
      intro x
      exact fullLogEmbeddingEquiv_equivariant F E g x))

@[simp] theorem fullLogEmbeddingRepresentationIso_apply
    (x : Additive ((𝓞 E)ˣ ⧸ NumberField.Units.torsion E)) :
    (fullLogEmbeddingRepresentationIso F E).hom.hom x = fullLogEmbeddingEquiv E x := rfl

/-- The resulting ordinary group cohomology isomorphism in every degree. -/
def fullLogEmbeddingCohomologyIso (n : ℕ) :
    groupCohomology (unitsModuloTorsionRepresentation F E) n ≅
      groupCohomology (fullLogUnitLatticeRepresentation F E) n :=
  (groupCohomology.functor NormalizedTwoCocycle.CoefficientScalars.{v}
    (E ≃ₐ[F] E) n).mapIso (fullLogEmbeddingRepresentationIso F E)

end Langlands.ClassField.Global
