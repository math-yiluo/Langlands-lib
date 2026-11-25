/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Yoneda

/-!
# Invertibility of mates along adjunctions with invertible unit

Let `L₁ ⊣ R₁` and `L₂ ⊣ R₂` be adjunctions and `α : G ⋙ L₂ ⟶ L₁ ⋙ H` an isomorphism
filling the square
```
  C₁ --L₁--> D₁
  |          |
  G          H
  v          v
  C₂ --L₂--> D₂
```
At `d`, the mate `R₁ ⋙ G ⟶ H ⋙ R₂` of `α` is the unit of `L₂ ⊣ R₂` at `G (R₁ d)`, followed by
`R₂` of `α`, followed by `R₂ H` of the counit `ε_d` of `L₁ ⊣ R₁`. Hence, if the unit of `L₂ ⊣ R₂` is
invertible, the mate is invertible at `d` as soon as `R₂ (H ε_d)` is
(`CategoryTheory.isIso_mateEquiv_app_of_isIso_map_counit`).

A morphism `φ : X ⟶ Y` is inverted by the right adjoint `R` of an adjunction `L ⊣ R` as soon as
composition with `φ` is bijective on morphisms out of the objects `L B`
(`CategoryTheory.Adjunction.isIso_map_of_bijective_comp`), by the Yoneda lemma.

-/

@[expose] public section

namespace CategoryTheory

open Category

section Mate

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  {G : A ⥤ C} {H : B ⥤ D} {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

/-- The mate `R₁ ⋙ G ⟶ H ⋙ R₂` of an isomorphism `α : G ⋙ L₂ ⟶ L₁ ⋙ H`, along adjunctions
`L₁ ⊣ R₁` and `L₂ ⊣ R₂` where the unit of the second is invertible, is invertible at `d` as soon
as `R₂ (H ε_d)` is, `ε` being the counit of `L₁ ⊣ R₁`: at `d` the mate is the unit of `L₂ ⊣ R₂`,
then `R₂` of `α`, then `R₂ (H ε_d)`. -/
theorem isIso_mateEquiv_app_of_isIso_map_counit [IsIso adj₂.unit] (α : TwoSquare G L₁ L₂ H)
    [IsIso α] (d : B) (h : IsIso (R₂.map (H.map (adj₁.counit.app d)))) :
    IsIso ((mateEquiv adj₁ adj₂ α).app d) := by
  simp only [mateEquiv_apply, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app, Functor.comp_map]
  dsimp only [Functor.comp_obj]
  simp only [Category.id_comp]
  have : IsIso (α.app (R₁.obj d)) := inferInstance
  have : IsIso (𝟙 (R₂.obj (H.obj d))) := inferInstance
  exact IsIso.comp_isIso

end Mate

namespace Adjunction

variable {C D : Type*} [Category* C] [Category* D] {L : C ⥤ D} {R : D ⥤ C}

/-- **Yoneda along an adjunction.** If composition with `φ : X ⟶ Y` is bijective on morphisms
out of every object `L B`, then `R φ` is an isomorphism: under `L ⊣ R`, composition with `R φ`
on morphisms out of `B` is composition with `φ` on morphisms out of `L B`. -/
theorem isIso_map_of_bijective_comp (adj : L ⊣ R) {X Y : D} (φ : X ⟶ Y)
    (h : ∀ B : C, Function.Bijective (fun x : L.obj B ⟶ X ↦ x ≫ φ)) : IsIso (R.map φ) := by
  refine isIso_of_yoneda_map_bijective _ fun B ↦ ?_
  have e : (fun x : B ⟶ R.obj X ↦ x ≫ R.map φ) =
      (adj.homEquiv B Y) ∘ (fun x : L.obj B ⟶ X ↦ x ≫ φ) ∘ (adj.homEquiv B X).symm := by
    funext x
    rw [Function.comp_apply, Function.comp_apply, Adjunction.homEquiv_naturality_right,
      Equiv.apply_symm_apply]
  rw [e]
  exact (adj.homEquiv B Y).bijective.comp ((h B).comp (adj.homEquiv B X).symm.bijective)

end Adjunction

end CategoryTheory
