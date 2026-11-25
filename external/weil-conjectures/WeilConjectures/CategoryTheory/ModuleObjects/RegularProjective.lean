/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod

/-!
# Projectivity of the regular module

Let `R` be a ring object in an abelian monoidal category `C`. If the unit `𝟙_ C` is projective,
then so is the regular module `R` (`CategoryTheory.Mod.projective_regular`): a morphism `R ⟶ N`
of `R`-modules is determined by the image of the unit, which lifts along any epimorphism.
-/

@[expose] public section

universe v u

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C] [MonoidalPreadditive C]
  {R : C} [MonObj R] [PreservesFiniteColimits (tensorLeft R)]

/-- The regular module `R` over a ring object `R` is projective when the unit is: a morphism
`R ⟶ N` is determined by the image of the unit, which lifts along any epimorphism. -/
theorem projective_regular [Projective (𝟙_ C)] : Projective (regular R) := by
  refine ⟨fun {M N} f e he ↦ ?_⟩
  have : (forget R : Mod C R ⥤ C).IsRightAdjoint := (freeForgetAdjunction R).isRightAdjoint
  have : (forget R : Mod C R ⥤ C).PreservesEpimorphisms :=
    NormalMonoCategory.preservesEpimorphisms_of_preservesCokernels _
  have : Epi e.hom := (forget R).map_epi e
  obtain ⟨y, hy⟩ := Projective.factors ((MonObj.one : 𝟙_ C ⟶ R) ≫ f.hom) e.hom
  refine ⟨regularLift M y, regular_hom_ext ?_⟩
  rw [comp_hom', ← Category.assoc, one_comp_regularLift, hy]

end CategoryTheory.Mod
