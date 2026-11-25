/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.RegularEnd

/-!
# Endomorphisms of the regular module are multiplications by global sections

For a commutative algebra object `R` of a braided preadditive monoidal category, every
endomorphism of the regular module `R` is the multiplication by a global section `𝟙 ⟶ R`: the
ring homomorphism `Γ R →+* End (Mod.regular R)` is surjective
(`CategoryTheory.Mod.regularEndRingHom_surjective`).
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]
  [MonoidalPreadditive C] [BraidedCategory C] {R : C} [MonObj R] [IsCommMonObj R]

/-- Every endomorphism `t` of the regular module `R` is the multiplication by the global section
`η ≫ t`. -/
lemma regularEndRingHom_surjective : Function.Surjective (regularEndRingHom (R := R)) :=
  fun t ↦ ⟨Γ.ofHom (η[R] ≫ t.asHom.hom), End.ext (regular_hom_ext (by
    rw [regularEndRingHom_apply, Γ.hom_ofHom, one_comp_regularLift_regular]))⟩

end CategoryTheory.Mod
