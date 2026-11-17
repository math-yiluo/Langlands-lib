import Mathlib.CategoryTheory.Monoidal.Grp

/-! # Group objects from uniquely lifted operations -/

noncomputable section

universe v u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.CategoryTheory.GroupObjectLift

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {X P : C}

/-- Specified lifts of operations give a monoid when composition is injective
on maps from the source and its cube. -/
@[instance_reducible]
def monObjOfInjective [MonObj X] (j : P ⟶ X)
    (hP : Function.Injective (fun f : P ⟶ P => f ≫ j))
    (hCube : Function.Injective (fun f : (P ⊗ P) ⊗ P ⟶ P => f ≫ j))
    (e : 𝟙_ C ⟶ P) (m : P ⊗ P ⟶ P)
    (he : e ≫ j = η[X]) (hm : m ≫ j = (j ⊗ₘ j) ≫ μ[X]) : MonObj P where
  one := e
  mul := m
  one_mul := by
    apply (cancel_epi (λ_ P).inv).mp
    apply hP
    simp only [Category.assoc, hm, ← tensorHom_id,
      tensorHom_comp_tensorHom_assoc, he, Category.id_comp]
    simp only [← lift_fst_comp_snd_comp, MonObj.lift_comp_one_left,
      leftUnitor_hom]
  mul_one := by
    apply (cancel_epi (ρ_ P).inv).mp
    apply hP
    simp only [Category.assoc, hm, ← id_tensorHom,
      tensorHom_comp_tensorHom_assoc, he, Category.id_comp]
    simp only [← lift_fst_comp_snd_comp, MonObj.lift_comp_one_right,
      rightUnitor_hom]
  mul_assoc := by
    apply hCube
    simpa only [← tensorHom_id, ← id_tensorHom, Category.assoc, hm,
      tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id,
      associator_naturality_assoc] using
      congrArg (fun f => ((j ⊗ₘ j) ⊗ₘ j) ≫ f) (MonObj.mul_assoc X)

/-- Add a lifted inverse to the preceding monoid construction. -/
@[instance_reducible]
def grpObjOfInjective [GrpObj X] (j : P ⟶ X)
    (hP : Function.Injective (fun f : P ⟶ P => f ≫ j))
    (hCube : Function.Injective (fun f : (P ⊗ P) ⊗ P ⟶ P => f ≫ j))
    (e : 𝟙_ C ⟶ P) (m : P ⊗ P ⟶ P) (w : P ⟶ P)
    (he : e ≫ j = η[X]) (hm : m ≫ j = (j ⊗ₘ j) ≫ μ[X])
    (hw : w ≫ j = j ≫ ι[X]) : GrpObj P where
  toMonObj := monObjOfInjective j hP hCube e m he hm
  inv := w
  left_inv := by
    apply hP
    change (lift w (𝟙 P) ≫ m) ≫ j = (toUnit P ≫ e) ≫ j
    simpa only [Category.assoc, hm, lift_map_assoc, hw, Category.id_comp, he]
      using GrpObj.lift_comp_inv_left j
  right_inv := by
    apply hP
    change (lift (𝟙 P) w ≫ m) ≫ j = (toUnit P ≫ e) ≫ j
    simpa only [Category.assoc, hm, lift_map_assoc, hw, Category.id_comp, he]
      using GrpObj.lift_comp_inv_right j


/-- The comparison map preserves the lifted unit and multiplication. -/
theorem isMonHom_grpObjOfInjective [GrpObj X] (j : P ⟶ X)
    (hP : Function.Injective (fun f : P ⟶ P => f ≫ j))
    (hCube : Function.Injective (fun f : (P ⊗ P) ⊗ P ⟶ P => f ≫ j))
    (e : 𝟙_ C ⟶ P) (m : P ⊗ P ⟶ P) (w : P ⟶ P)
    (he : e ≫ j = η[X]) (hm : m ≫ j = (j ⊗ₘ j) ≫ μ[X])
    (hw : w ≫ j = j ≫ ι[X]) :
    letI := grpObjOfInjective j hP hCube e m w he hm hw
    IsMonHom j := by
  let _ := grpObjOfInjective j hP hCube e m w he hm hw
  exact ⟨he, hm⟩

end Langlands.CategoryTheory.GroupObjectLift
