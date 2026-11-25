/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.Combinatorics.Quiver.ReflQuiver

/-!
# Adjoints of morphisms composed with conjugate transformations

`CategoryTheory.Adjunction.homEquiv_comp_conjugateEquiv_app`: composing the adjoint of a morphism
with a conjugate transformation is the adjoint of the composite with the original transformation,
and its version `CategoryTheory.Adjunction.homEquiv_homEquiv_comp_conjugateIsoEquiv_app` for
composite adjunctions.
-/

@[expose] public section

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}

/-- Composing an adjoint with a conjugate transformation is the adjoint of the composite with
the original transformation: for `α : L₂ ⟶ L₁` and `f : L₁ M ⟶ N`,
`adj₁.homEquiv f ≫ (conjugateEquiv adj₁ adj₂ α).app N = adj₂.homEquiv (α.app M ≫ f)`. -/
lemma Adjunction.homEquiv_comp_conjugateEquiv_app (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (α : L₂ ⟶ L₁) {M : C} {N : D} (f : L₁.obj M ⟶ N) :
    adj₁.homEquiv M N f ≫ (conjugateEquiv adj₁ adj₂ α).app N =
      adj₂.homEquiv M N (α.app M ≫ f) := by
  rw [conjugateEquiv_apply_app, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    ← adj₂.unit_naturality_assoc]
  congr 1
  simp only [← Functor.map_comp]
  congr 1
  rw [α.naturality_assoc, Functor.map_comp, Category.assoc, adj₁.counit_naturality,
    adj₁.left_triangle_components_assoc]

/-- `Adjunction.homEquiv_comp_conjugateEquiv_app` for composite adjunctions and the conjugate of
the inverse of an isomorphism of composite left adjoints. -/
lemma Adjunction.homEquiv_homEquiv_comp_conjugateIsoEquiv_app {C₁ C₂ C₃ C₄ : Type*}
    [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄] {A : C₁ ⥤ C₂} {A' : C₂ ⥤ C₁}
    {B : C₂ ⥤ C₃} {B' : C₃ ⥤ C₂} {E : C₁ ⥤ C₄} {E' : C₄ ⥤ C₁} {G : C₄ ⥤ C₃} {G' : C₃ ⥤ C₄}
    (a : A ⊣ A') (b : B ⊣ B') (e : E ⊣ E') (g : G ⊣ G') (σ : A ⋙ B ≅ E ⋙ G) {M : C₁}
    {N : C₃} (f : B.obj (A.obj M) ⟶ N) :
    a.homEquiv M (B'.obj N) (b.homEquiv (A.obj M) N f) ≫
        ((conjugateIsoEquiv (a.comp b) (e.comp g) σ.symm).app N).hom =
      e.homEquiv M (G'.obj N) (g.homEquiv (E.obj M) N (σ.inv.app M ≫ f)) := by
  have h := homEquiv_comp_conjugateEquiv_app (a.comp b) (e.comp g) σ.inv f
  simp only [comp_homEquiv] at h
  exact h

end CategoryTheory
