/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso

/-!

# Transposes through a composite of right adjoints

Let `α : R₁ ≅ R ⋙ R'` identify the right adjoint of `L₁ ⊣ R₁` with the composite of the right
adjoints of `L' ⊣ R'` and `L ⊣ R`, and let `e : L₁ ≅ L' ⋙ L` be the conjugate identification of
the left adjoints. The transpose of `f : A ⟶ R₁ K` under `L₁ ⊣ R₁` is computed through `e` and the
transpose of `f ≫ α_K` under `L' ⊣ R'`
(`CategoryTheory.Adjunction.conjugateIsoEquiv_symm_inv_app_comp_map_homEquiv_symm_comp_counit`).

-/

@[expose] public section

namespace CategoryTheory.Adjunction

/-- Let `α : R₁ ≅ R ⋙ R'` identify the right adjoint of `L₁ ⊣ R₁` with the composite of the right
adjoints of `L' ⊣ R'` and `L ⊣ R`, and let `e : L₁ ≅ L' ⋙ L` be the conjugate identification of
the left adjoints. Then the transpose of `f : A ⟶ R₁ K` under `L₁ ⊣ R₁` is computed through `e`
and the transpose `f' : L' A ⟶ R K` of `f ≫ α_K` under `L' ⊣ R'`:
```
L₁ A ----e⁻¹----> L (L' A) --L f'--> L (R K)
  |                                       |
L₁ f                                      ε
  v                                       v
L₁ (R₁ K) -------------ε₁-------------> K
```
-/
lemma conjugateIsoEquiv_symm_inv_app_comp_map_homEquiv_symm_comp_counit
    {C M D : Type*} [Category* C] [Category* M] [Category* D] {L₁ : C ⥤ D} {R₁ : D ⥤ C}
    {L' : C ⥤ M} {R' : M ⥤ C} {L : M ⥤ D} {R : D ⥤ M} (adj₁ : L₁ ⊣ R₁) (adj' : L' ⊣ R')
    (adj : L ⊣ R) (α : R₁ ≅ R ⋙ R') {A : C} {K : D} (f : A ⟶ R₁.obj K) :
    ((conjugateIsoEquiv adj₁ (adj'.comp adj)).symm α).inv.app A ≫
        L.map ((adj'.homEquiv _ _).symm (f ≫ α.hom.app K)) ≫ adj.counit.app K =
      L₁.map f ≫ adj₁.counit.app K := by
  have h₁ := conjugateEquiv_counit_symm adj₁ (adj'.comp adj) α.hom K
  have h₂ := ((conjugateIsoEquiv adj₁ (adj'.comp adj)).symm α).inv.naturality f
  rw [Adjunction.comp_counit_app] at h₁
  dsimp only [Functor.comp_map, Functor.comp_obj] at h₁ h₂
  rw [Adjunction.homEquiv_counit]
  simp only [Functor.map_comp, Category.assoc]
  rw [h₁, ← reassoc_of% h₂]
  exact congrArg (L₁.map f ≫ ·)
    (((conjugateIsoEquiv adj₁ (adj'.comp adj)).symm α).inv_hom_id_app_assoc _ _)

end CategoryTheory.Adjunction
