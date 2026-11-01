import Mathlib.CategoryTheory.Monoidal.Grp

/-! # Restricting group objects along monomorphisms -/

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.CategoryTheory.GroupObjectDescent

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {X P : C}

/-- Restrict a monoid structure along a monomorphism when its unit and
multiplication have specified lifts. -/
@[instance_reducible]
def monObjOfMono [MonObj X] (j : P ⟶ X) [Mono j]
    (e : 𝟙_ C ⟶ P) (m : P ⊗ P ⟶ P)
    (he : e ≫ j = η[X]) (hm : m ≫ j = (j ⊗ₘ j) ≫ μ[X]) : MonObj P where
  one := e
  mul := m
  one_mul := by
    apply (cancel_mono j).mp
    simp only [Category.assoc, hm, ← tensorHom_id,
      tensorHom_comp_tensorHom_assoc, he, Category.id_comp]
    simp only [← lift_fst_comp_snd_comp, MonObj.lift_comp_one_left,
      leftUnitor_hom]
  mul_one := by
    apply (cancel_mono j).mp
    simp only [Category.assoc, hm, ← id_tensorHom,
      tensorHom_comp_tensorHom_assoc, he, Category.id_comp]
    simp only [← lift_fst_comp_snd_comp, MonObj.lift_comp_one_right,
      rightUnitor_hom]
  mul_assoc := by
    apply (cancel_mono j).mp
    simpa only [← tensorHom_id, ← id_tensorHom, Category.assoc, hm,
      tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id,
      associator_naturality_assoc] using
      congrArg (fun f => ((j ⊗ₘ j) ⊗ₘ j) ≫ f) (MonObj.mul_assoc X)

/-- Restrict a group structure using specified unit, multiplication and inverse
maps. These three operations are retained definitionally. -/
@[instance_reducible]
def grpObjOfMono [GrpObj X] (j : P ⟶ X) [Mono j]
    (e : 𝟙_ C ⟶ P) (m : P ⊗ P ⟶ P) (w : P ⟶ P)
    (he : e ≫ j = η[X]) (hm : m ≫ j = (j ⊗ₘ j) ≫ μ[X])
    (hw : w ≫ j = j ≫ ι[X]) : GrpObj P where
  toMonObj := monObjOfMono j e m he hm
  inv := w
  left_inv := by
    apply (cancel_mono j).mp
    change (lift w (𝟙 P) ≫ m) ≫ j = (toUnit P ≫ e) ≫ j
    simpa only [Category.assoc, hm, lift_map_assoc, hw, Category.id_comp, he]
      using GrpObj.lift_comp_inv_left j
  right_inv := by
    apply (cancel_mono j).mp
    change (lift (𝟙 P) w ≫ m) ≫ j = (toUnit P ≫ e) ≫ j
    simpa only [Category.assoc, hm, lift_map_assoc, hw, Category.id_comp, he]
      using GrpObj.lift_comp_inv_right j

/-- The monomorphism is a homomorphism for the restricted group structure. -/
theorem isMonHom_grpObjOfMono [GrpObj X] (j : P ⟶ X) [Mono j]
    (e : 𝟙_ C ⟶ P) (m : P ⊗ P ⟶ P) (w : P ⟶ P)
    (he : e ≫ j = η[X]) (hm : m ≫ j = (j ⊗ₘ j) ≫ μ[X])
    (hw : w ≫ j = j ≫ ι[X]) :
    letI := grpObjOfMono j e m w he hm hw
    IsMonHom j := by
  let := grpObjOfMono j e m w he hm hw
  exact ⟨he, hm⟩

/-- Commutativity descends along a monomorphic monoid homomorphism. -/
theorem commMonObjOfMono [BraidedCategory C] [MonObj P] [MonObj X] [IsCommMonObj X]
    (j : P ⟶ X) [Mono j] [IsMonHom j] : IsCommMonObj P where
  mul_comm := by
    apply (cancel_mono j).mp
    simp only [Category.assoc, IsMonHom.mul_hom]
    rw [← BraidedCategory.braiding_naturality_assoc, IsCommMonObj.mul_comm]

end Langlands.CategoryTheory.GroupObjectDescent
