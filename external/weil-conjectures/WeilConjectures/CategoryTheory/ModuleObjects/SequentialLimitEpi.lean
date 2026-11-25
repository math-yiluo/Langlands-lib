/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

/-!
# Sequential limits of epimorphisms of module objects

Let `C` be an abelian monoidal category and `R` a monoid object such that `R ⊗ -` is right
exact. If in `C` the projection `lim Xₙ ⟶ X₀` of a tower of epimorphisms is an epimorphism, the
same holds in `Mod C R` (`CategoryTheory.Mod.epiπAppZeroOfEpi`): the forgetful functor
`Mod C R ⥤ C` is a right adjoint (`CategoryTheory.Mod.freeForgetAdjunction`), so it preserves
limits, and it preserves and reflects epimorphisms. Hence `Mod C R` satisfies countable AB4\*
when `C` does in this form (`CategoryTheory.CountableAB4Star.of_epi_π_app_zero`).
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C] [MonoidalPreadditive C]
  {R : C} [MonObj R] [PreservesFiniteColimits (tensorLeft R)]

/-- If the projection `lim Xₙ ⟶ X₀` of a tower of epimorphisms is an epimorphism in `C`, it is
one in `Mod C R`. -/
lemma epiπAppZeroOfEpi [HasLimitsOfShape ℕᵒᵖ C] (h : EpiπAppZeroOfEpi C) :
    EpiπAppZeroOfEpi (Mod C R) := by
  intro F c hc hF
  have : (forget R : Mod C R ⥤ C).IsRightAdjoint := (freeForgetAdjunction R).isRightAdjoint
  have : (forget R : Mod C R ⥤ C).PreservesEpimorphisms :=
    NormalMonoCategory.preservesEpimorphisms_of_preservesCokernels _
  apply (forget R : Mod C R ⥤ C).epi_of_epi_map
  exact h (F := F ⋙ forget R) (isLimitOfPreserves (forget R) hc) fun n ↦ (forget R).map_epi _

end CategoryTheory.Mod
