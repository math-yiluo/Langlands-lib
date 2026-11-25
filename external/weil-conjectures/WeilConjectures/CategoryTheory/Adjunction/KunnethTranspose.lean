/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.KunnethMap

/-!

# Künneth maps as transposes

Let `F ⊣ G` be an adjunction between monoidal categories with `F` oplax monoidal, and let
`μ : G M ⊗ G N ⟶ G (M ⊗ N)` be a lax tensor map whose transpose is the tensor product of the
counits. A Künneth map `(b₁ ⊗ b₂) ≫ μ` is then the transpose of `F (U₁ ⊗ U₂) ⟶ F U₁ ⊗ F U₂`
followed by the tensor product of the transposes of the `bᵢ`
(`CategoryTheory.Adjunction.tensorHom_comp_eq_homEquiv_δ`). Such transposes are compatible with
the restriction of `F ⊣ G` to full monoidal subcategories
(`CategoryTheory.Adjunction.ι_map_homEquiv_δ_tensorHom_restrictFullyFaithful`).

-/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
  {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) [F.OplaxMonoidal]

/-- A tensor product of morphisms `bᵢ : Uᵢ ⟶ G Mᵢ` followed by a lax tensor map `μ` of `G` whose
transpose is the tensor product of the counits is the transpose of the oplax structure of `F`
followed by the tensor product of the transposes `cᵢ` of the `bᵢ`:
```
U₁ ⊗ U₂ ──b₁ ⊗ b₂──▶ G M ⊗ G N          F (U₁ ⊗ U₂) ──δ──▶ F U₁ ⊗ F U₂
                         │ μ       ↭                              │ c₁ ⊗ c₂
                         ▼                                        ▼
                    G (M ⊗ N)                                   M ⊗ N
```
the left composite is the transpose of the right one. -/
lemma tensorHom_comp_eq_homEquiv_δ (μ : ∀ M N, G.obj M ⊗ G.obj N ⟶ G.obj (M ⊗ N))
    (hμ : ∀ M N, F.map (μ M N) ≫ adj.counit.app (M ⊗ N) =
      Functor.OplaxMonoidal.δ F _ _ ≫ (adj.counit.app M ⊗ₘ adj.counit.app N))
    {U₁ U₂ : D} {M N : C} (b₁ : U₁ ⟶ G.obj M) (b₂ : U₂ ⟶ G.obj N) (c₁ : F.obj U₁ ⟶ M)
    (c₂ : F.obj U₂ ⟶ N) (hb₁ : F.map b₁ ≫ adj.counit.app M = c₁)
    (hb₂ : F.map b₂ ≫ adj.counit.app N = c₂) :
    (b₁ ⊗ₘ b₂) ≫ μ M N = adj.homEquiv _ _ (Functor.OplaxMonoidal.δ F U₁ U₂ ≫ (c₁ ⊗ₘ c₂)) := by
  apply (adj.homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply, homEquiv_counit, Functor.map_comp, Category.assoc, hμ,
    ← Functor.OplaxMonoidal.δ_natural_assoc, tensorHom_comp_tensorHom, hb₁, hb₂]

section Restrict

variable {P : ObjectProperty C} [P.IsMonoidal] {Q : ObjectProperty D} [Q.IsMonoidal]
  {F' : D ⥤ C} [F'.Monoidal] {G' : C ⥤ D} (adj' : F' ⊣ G')
  (hF : ∀ X : Q.FullSubcategory, P (F'.obj X.obj)) (hG : ∀ X : P.FullSubcategory, Q (G'.obj X.obj))

/-- The Künneth transpose of the restriction of an adjunction `F ⊣ G` to full monoidal
subcategories is the Künneth transpose of `F ⊣ G`: for `cᵢ : F Uᵢ ⟶ Aᵢ` in the subcategory,
```
ι (transpose of  F (U₁ ⊗ U₂) ──δ──▶ F U₁ ⊗ F U₂ ──c₁ ⊗ c₂──▶ A₁ ⊗ A₂  in the subcategories)
  = transpose of  F (ι U₁ ⊗ ι U₂) ──δ──▶ F (ι U₁) ⊗ F (ι U₂) ──ι c₁ ⊗ ι c₂──▶ ι A₁ ⊗ ι A₂.
``` -/
lemma ι_map_homEquiv_δ_tensorHom_restrictFullyFaithful {U₁ U₂ : Q.FullSubcategory}
    {A₁ A₂ : P.FullSubcategory} (c₁ : (P.lift (Q.ι ⋙ F') hF).obj U₁ ⟶ A₁)
    (c₂ : (P.lift (Q.ι ⋙ F') hF).obj U₂ ⟶ A₂) :
    Q.ι.map ((adj'.restrictFullyFaithful Q.fullyFaithfulι P.fullyFaithfulι
      (P.liftCompιIso (Q.ι ⋙ F') hF).symm (Q.liftCompιIso (P.ι ⋙ G') hG).symm).homEquiv _ _
        (Functor.OplaxMonoidal.δ (P.lift (Q.ι ⋙ F') hF) U₁ U₂ ≫ (c₁ ⊗ₘ c₂))) =
      adj'.homEquiv _ _
        (Functor.OplaxMonoidal.δ F' U₁.obj U₂.obj ≫ (P.ι.map c₁ ⊗ₘ P.ι.map c₂)) := by
  rw [restrictFullyFaithful_homEquiv_apply, Functor.FullyFaithful.map_preimage, homEquiv_unit]
  simp only [ObjectProperty.liftCompιIso, Iso.symm_hom, Iso.refl_inv, Functor.map_comp]
  erw [Functor.map_id, Category.id_comp, Category.comp_id]
  rfl

end Restrict

end CategoryTheory.Adjunction
