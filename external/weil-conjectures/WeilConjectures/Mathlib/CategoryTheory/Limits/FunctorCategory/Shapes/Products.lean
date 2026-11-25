/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Naturality of the evaluation of a product of functors

For a family of functors `F : α → (D ⥤ C)`, `CategoryTheory.Limits.piObjIso` identifies
`(∏ᶜ F).obj d` with `∏ᶜ fun t ↦ (F t).obj d`. This file records that this identification is
natural in `d`, and deduces that a finite product of functors sends a morphism to an
epimorphism as soon as every factor does.

## Main results

- `CategoryTheory.Limits.piObj_map`: `(∏ᶜ F).map φ` is `Pi.map fun t ↦ (F t).map φ`,
  transported along `CategoryTheory.Limits.piObjIso`.
- `CategoryTheory.Limits.epi_piObj_map`: for a finite family `F` of functors into a
  preadditive category with finite products, `(∏ᶜ F).map φ` is an epimorphism as soon as
  every `(F t).map φ` is one.

-/

@[expose] public section

universe w v v₁ u u₁

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {D : Type u₁} [Category.{v₁} D] {α : Type w}

/-- **The evaluation of a product of functors is natural.** For `F : α → (D ⥤ C)` and
`φ : P ⟶ Q` in `D`, the square
```
              (∏ᶜ F).obj P ------------(∏ᶜ F).map φ------------> (∏ᶜ F).obj Q
                   |                                                  |
            piObjIso F P ≅                                     piObjIso F Q ≅
                   ↓                                                  ↓
    ∏ᶜ (fun t ↦ (F t).obj P) --Pi.map (fun t ↦ (F t).map φ)--> ∏ᶜ (fun t ↦ (F t).obj Q)
```
commutes. -/
lemma piObj_map [HasLimitsOfShape (Discrete α) C] (F : α → D ⥤ C) {P Q : D} (φ : P ⟶ Q) :
    (∏ᶜ F).map φ =
      (piObjIso F P).hom ≫ Pi.map (fun t ↦ (F t).map φ) ≫ (piObjIso F Q).inv := by
  rw [← cancel_mono (piObjIso F Q).hom]
  refine Pi.hom_ext _ _ fun t ↦ ?_
  simp only [Category.assoc, piObjIso_hom_comp_π, piObjIso_inv_comp_π, Pi.map_π,
    piObjIso_hom_comp_π_assoc]
  exact NatTrans.naturality _ _

/-- If `φ : P ⟶ Q` is sent to an epimorphism by every member of a finite family `F` of
functors into a preadditive category with finite products, then it is sent to an epimorphism
by the product `∏ᶜ F`. -/
lemma epi_piObj_map [Preadditive C] [HasFiniteProducts C] [Finite α] (F : α → D ⥤ C)
    {P Q : D} (φ : P ⟶ Q) [∀ t, Epi ((F t).map φ)] : Epi ((∏ᶜ F).map φ) := by
  have : HasFiniteBiproducts C := .of_hasFiniteProducts
  rw [piObj_map]
  infer_instance

end CategoryTheory.Limits
