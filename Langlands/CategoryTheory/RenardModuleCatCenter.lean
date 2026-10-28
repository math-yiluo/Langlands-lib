import Langlands.CategoryTheory.RenardModuleCatCenterStatements
import Mathlib.Algebra.Module.ULift

/-!
# Renard A.X: proof of the center identification for unital module categories

The proof evaluates natural endomorphisms on the lifted regular module and
reconstructs their components by naturality. The scalar-action ring homomorphism
is the one in the published statement module.
-/

universe u v

open CategoryTheory
open scoped ModuleCat.Algebra

namespace Langlands.Renard

variable (R : Type u) [Ring R]

private def regularTo (M : ModuleCat.{max u v} R) (m : M) :
    ModuleCat.of R (ULift.{v} R) ⟶ M :=
  ModuleCat.ofHom
    { toFun := fun r => r.down • m
      map_add' := fun r s => add_smul r.down s.down m
      map_smul' := fun r s => mul_smul r s.down m }

private def centerEvaluation (z : CatCenter (ModuleCat.{max u v} R)) : R :=
  ((z.app (ModuleCat.of R (ULift.{v} R))).hom (ULift.up 1)).down

private theorem center_component (z : CatCenter (ModuleCat.{max u v} R))
    (M : ModuleCat.{max u v} R) (m : M) :
    (z.app M).hom m = centerEvaluation R z • m := by
  have h := congrArg (fun f => f.hom (ULift.up (1 : R)))
    (CatCenter.naturality z (regularTo R M m))
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, regularTo,
    ModuleCat.hom_ofHom, LinearMap.coe_mk, AddHom.coe_mk, one_smul,
    centerEvaluation] using h

private theorem centerEvaluation_mem_center (z : CatCenter (ModuleCat.{max u v} R)) :
    centerEvaluation R z ∈ Subring.center R := by
  rw [Subring.mem_center_iff]
  intro r
  have h := (z.app (ModuleCat.of R (ULift.{v} R))).hom.map_smul r
    (ULift.up (1 : R))
  have hc := center_component R z (ModuleCat.of R (ULift.{v} R)) (ULift.up r)
  have hd := congrArg ULift.down h
  change ((z.app (ModuleCat.of R (ULift.{v} R))).hom (r • ULift.up (1 : R))).down =
    r * centerEvaluation R z at hd
  have hr : r • ULift.up (1 : R) = ULift.up r := by
    apply ULift.ext
    exact mul_one r
  rw [hr, hc] at hd
  exact hd.symm

/-- The existing scalar-action map has the component formula in Renard A.X. -/
theorem moduleCatCenterScalarComponent :
    ModuleCatCenterScalarComponentStatement.{u, v} R := by
  intro c M m
  rfl

/-- Renard A.X: the canonical scalar-action map is bijective. -/
theorem moduleCatCenterBijective :
    ModuleCatCenterBijectiveStatement.{u, v} R := by
  constructor
  · intro c d h
    apply Subtype.ext
    have he := congrArg
      (fun z : CatCenter (ModuleCat.{max u v} R) => centerEvaluation R z) h
    change c.val * 1 = d.val * 1 at he
    simpa only [mul_one] using he
  · intro z
    refine ⟨⟨centerEvaluation R z, centerEvaluation_mem_center R z⟩, ?_⟩
    apply CatCenter.ext
    intro M
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    change centerEvaluation R z • m = (z.app M).hom m
    exact (center_component R z M m).symm

/-- Renard A.X: the ring isomorphism has exactly the existing scalar-action
ring homomorphism as its forward map. -/
theorem moduleCatCenterRingEquiv :
    ModuleCatCenterRingEquivStatement.{u, v} R := by
  refine ⟨RingEquiv.ofBijective
    (Linear.toCatCenter (Subring.center R) (ModuleCat.{max u v} R))
    (moduleCatCenterBijective.{u, v} R), ?_⟩
  rfl

/-- Renard A.X: the center of the category of unital modules is canonically
identified with the ring center, through the stated scalar-action map. -/
theorem moduleCatCenterIdentification :
    ModuleCatCenterIdentificationStatement.{u, v} R :=
  ⟨moduleCatCenterBijective.{u, v} R, moduleCatCenterRingEquiv.{u, v} R⟩

end Langlands.Renard
