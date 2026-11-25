/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.Preadditive
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Conv

/-!
# Global sections acting on the regular module

For a commutative algebra object `R` of a braided preadditive monoidal category, a global
section `s : 𝟙 ⟶ R` acts on the regular module `R` by multiplication. This is a ring
homomorphism `Γ R →+* End (Mod.regular R)` (`CategoryTheory.Mod.regularEndRingHom`).
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Preadditive

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {R : C} [MonObj R]

/-- `regularLift` on the regular module, with the global section seen as a morphism to `R`. -/
lemma one_comp_regularLift_regular (x : 𝟙_ C ⟶ R) :
    (η : 𝟙_ C ⟶ R) ≫ (regularLift (regular R) x).hom = x :=
  one_comp_regularLift (regular R) x

variable [Preadditive C] [MonoidalPreadditive C] [BraidedCategory C] [IsCommMonObj R]

/-- The multiplication by a global section `s : 𝟙 ⟶ R` of a commutative algebra object `R`, as
an endomorphism `R ⟶ R` of the regular module: a ring homomorphism. -/
def regularEndRingHom : Γ R →+* End (regular R) where
  toFun s := .of (regularLift (regular R) s.hom)
  map_one' := End.ext (regular_hom_ext (by
    rw [one_comp_regularLift_regular, Γ.one_hom, End.one_asHom, Mod.id_hom']
    exact (Category.comp_id _).symm))
  map_mul' s t := End.ext (regular_hom_ext (by
    rw [one_comp_regularLift_regular, End.mul_asHom, Mod.comp_hom']
    erw [← Category.assoc, one_comp_regularLift_regular]
    rw [Γ.mul_comm', Γ.mul_hom]
    change _ = t.hom ≫ (ρ_ R).inv ≫ R ◁ s.hom ≫ μ
    rw [rightUnitor_inv_naturality_assoc, ← unitors_inv_equal, ← tensorHom_def_assoc]))
  map_zero' := End.ext (regular_hom_ext (by
    rw [one_comp_regularLift_regular, Γ.zero_hom, End.zero_asHom, zero_hom]
    exact Limits.comp_zero.symm))
  map_add' s t := End.ext (regular_hom_ext (by
    rw [one_comp_regularLift_regular, Γ.add_hom, End.add_asHom, add_hom]
    erw [comp_add, one_comp_regularLift_regular, one_comp_regularLift_regular]))

@[simp]
lemma regularEndRingHom_apply (s : Γ R) :
    regularEndRingHom s = .of (regularLift (regular R) s.hom) :=
  rfl

end CategoryTheory.Mod
