/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-!
# The projection map at the unit of an adjunction with lax monoidal right adjoint

Let `adj : F ⊣ G` be an adjunction between monoidal categories, with `F : C ⥤ D` and `G` lax
monoidal. The *unit projection map* is the composite
```
K ⊗ G 𝟙 ──η ▷ _──▶ G (F K) ⊗ G 𝟙 ──μ──▶ G (F K ⊗ 𝟙) ──G ρ──▶ G (F K).
```
For extension and restriction of scalars along a ring morphism `R ⟶ S` it is the map
`K ⊗_R S ⟶ S ⊗_R K`.

## Main results

- `CategoryTheory.Adjunction.homEquiv_symm_unitProjection`: if the adjunction is monoidal, the
  transpose of the unit projection map is `δ` followed by the counit at `𝟙` and the unitor.
- `CategoryTheory.Adjunction.map_unitProjection_comp_mateEquiv`: the unit projection maps are
  compatible with oplax monoidal functors `U` and `V` and an isomorphism `F ⋙ V ≅ U ⋙ F'`
  compatible with the comonoidal structures.
- `CategoryTheory.NatTrans.IsMonoidal.δ_comp_tensorHom`: a monoidal natural transformation
  between strong monoidal functors is compatible with `δ`.
- `CategoryTheory.Adjunction.unitProjection_comp_map_comp_app`: the unit projection maps are
  compatible with lax monoidal functors `I` and `J` and a monoidal transformation
  `J ⋙ G ⟶ G₂ ⋙ I`.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [G.LaxMonoidal]

/-- The projection map `K ⊗ G 𝟙 ⟶ G (F K)` of an adjunction `F ⊣ G` with lax monoidal right
adjoint: the unit of the adjunction, followed by `μ` and by the right unitor. -/
def unitProjection (K : C) : K ⊗ G.obj (𝟙_ D) ⟶ G.obj (F.obj K) :=
  (adj.unit.app K ▷ _) ≫ μ G _ _ ≫ G.map (ρ_ _).hom

/-- The transpose of the unit projection map `K ⊗ G 𝟙 ⟶ G (F K)` of a monoidal adjunction is
`F (K ⊗ G 𝟙) ──δ──▶ F K ⊗ F (G 𝟙) ──ε──▶ F K ⊗ 𝟙 ──ρ──▶ F K`. -/
lemma homEquiv_symm_unitProjection [F.OplaxMonoidal] [adj.IsMonoidal] (K : C) :
    (adj.homEquiv _ _).symm (adj.unitProjection K) =
      δ F K (G.obj (𝟙_ D)) ≫ (F.obj K ◁ adj.counit.app (𝟙_ D)) ≫ (ρ_ _).hom := by
  rw [homEquiv_counit, unitProjection, F.map_comp, F.map_comp, Category.assoc, Category.assoc,
    adj.counit_naturality, map_μ_comp_counit_app_tensor_assoc]
  erw [← δ_natural_left_assoc]
  rw [tensorHom_def, Category.assoc, ← comp_whiskerRight_assoc]
  erw [adj.left_triangle_components K, MonoidalCategory.id_whiskerRight, Category.id_comp]
  rfl

section WhiskerRight

variable (E : Type*) [Category* E]

/-- The unit projection map of the postcomposition adjunction `F ∘ - ⊣ G ∘ -` is computed
objectwise. -/
lemma whiskerRight_unitProjection_app (P : E ⥤ C) (U : E) :
    ((adj.whiskerRight E).unitProjection P).app U = adj.unitProjection (P.obj U) := by
  simp [unitProjection, Adjunction.whiskerRight]

/-- The unit projection map of the postcomposition adjunction `F ∘ - ⊣ G ∘ -` is an isomorphism
if the one of `F ⊣ G` is. -/
instance isIso_whiskerRight_unitProjection [∀ K, IsIso (adj.unitProjection K)] (P : E ⥤ C) :
    IsIso ((adj.whiskerRight E).unitProjection P) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro U
  rw [whiskerRight_unitProjection_app]
  infer_instance

end WhiskerRight

section Mate

variable {C' D' : Type*} [Category* C'] [Category* D'] [MonoidalCategory C']
  [MonoidalCategory D'] {F' : C' ⥤ D'} {G' : D' ⥤ C'} (adj' : F' ⊣ G') [G'.LaxMonoidal]
  {U : C ⥤ C'} {V : D ⥤ D'}

/-- **The unit projection maps are compatible with base change.** Let `U` and `V` be oplax
monoidal functors and `e : F ⋙ V ≅ U ⋙ F'` an isomorphism compatible with the comonoidal
structures, with mate `α : G ⋙ U ⟶ V ⋙ G'`. Then the square
```
U (K ⊗ G 𝟙) ──U π──▶ U G (F K) ──α──▶ G' V (F K) ──G' e──▶ G' F' (U K)
      │                                                   ‖
      δ                                                   ‖
      ▼                                                   ‖
U K ⊗ U G 𝟙 ──α──▶ U K ⊗ G' V 𝟙 ──η──▶ U K ⊗ G' 𝟙 ──π──▶ G' F' (U K)
```
commutes. -/
lemma map_unitProjection_comp_mateEquiv [F.OplaxMonoidal] [adj.IsMonoidal] [F'.OplaxMonoidal]
    [adj'.IsMonoidal] [U.OplaxMonoidal] [V.OplaxMonoidal] (e : F ⋙ V ≅ U ⋙ F')
    (he : ∀ A B : C, δ (F ⋙ V) A B ≫ (e.hom.app A ⊗ₘ e.hom.app B) =
      e.hom.app (A ⊗ B) ≫ δ (U ⋙ F') A B) (K : C) :
    U.map (adj.unitProjection K) ≫ (mateEquiv adj adj' e.inv).app (F.obj K) ≫
        G'.map (e.hom.app K) =
      δ U K (G.obj (𝟙_ D)) ≫
        (U.obj K ◁ ((mateEquiv adj adj' e.inv).app (𝟙_ D) ≫ G'.map (η V))) ≫
        adj'.unitProjection (U.obj K) := by
  apply (adj'.homEquiv _ _).symm.injective
  have h₁ := adj'.homEquiv_symm_unitProjection (U.obj K)
  have h₂ := adj.homEquiv_symm_unitProjection K
  have hδ := he K (G.obj (𝟙_ D))
  have hm (d : D) := mateEquiv_counit adj adj' e.inv d
  have h₃ := e.inv.naturality (adj.unitProjection K)
  rw [Functor.OplaxMonoidal.comp_δ, Functor.OplaxMonoidal.comp_δ] at hδ
  rw [homEquiv_counit] at h₁ h₂
  dsimp at h₃ hm hδ
  rw [homEquiv_counit, homEquiv_counit, F'.map_comp, F'.map_comp, Category.assoc,
    Category.assoc, adj'.counit_naturality, reassoc_of% hm, reassoc_of% h₃, ← V.map_comp_assoc,
    h₂, F'.map_comp, F'.map_comp, Category.assoc, Category.assoc]
  erw [h₁]
  have hδ' : F'.map (δ U K (G.obj (𝟙_ D))) ≫ δ F' (U.obj K) (U.obj (G.obj (𝟙_ D))) =
      e.inv.app _ ≫ (V.map (δ F K (G.obj (𝟙_ D))) ≫ δ V (F.obj K) (F.obj (G.obj (𝟙_ D)))) ≫
        (e.hom.app K ⊗ₘ e.hom.app (G.obj (𝟙_ D))) := by
    rw [hδ, Iso.inv_hom_id_app_assoc]
  erw [← δ_natural_right_assoc]
  rw [reassoc_of% hδ']
  congr 1
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, F'.map_comp, Category.assoc]
  erw [adj'.counit_naturality, reassoc_of% (hm (𝟙_ D))]
  rw [tensorHom_def'_assoc, ← whisker_exchange_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
    Iso.hom_inv_id_app_assoc]
  erw [rightUnitor_naturality]
  simp only [Functor.map_comp, Category.assoc, MonoidalCategory.whiskerLeft_comp,
    δ_natural_right_assoc, right_unitality_hom_assoc]

end Mate

section Restriction

variable {C₂ D₂ : Type*} [Category* C₂] [Category* D₂] [MonoidalCategory C₂]
  [MonoidalCategory D₂] {F₂ : C₂ ⥤ D₂} {G₂ : D₂ ⥤ C₂} (adj₂ : F₂ ⊣ G₂) [G₂.LaxMonoidal]
  {I : C₂ ⥤ C} {J : D₂ ⥤ D} [I.LaxMonoidal] [J.LaxMonoidal]

/-- **The unit projection maps are compatible with lax monoidal functors.** Let `I` and `J` be
lax monoidal functors and `θ : J ⋙ G ⟶ G₂ ⋙ I` a monoidal natural transformation. Let
`β : F (I K) ⟶ J (F₂ K)` be compatible with the units of the adjunctions. Then
```
I K ⊗ G 𝟙 ─────────π────────▶ G (F (I K)) ──G β──▶ G (J (F₂ K)) ──θ──▶ I (G₂ (F₂ K))
      │                                                                   ‖
  I K ◁ (G ε ≫ θ)                                                         ‖
      ▼                                                                   ‖
I K ⊗ I (G₂ 𝟙) ──μ──▶ I (K ⊗ G₂ 𝟙) ──────────────I π─────────────▶ I (G₂ (F₂ K))
```
commutes. -/
lemma unitProjection_comp_map_comp_app (θ : J ⋙ G ⟶ G₂ ⋙ I) [NatTrans.IsMonoidal θ] (K : C₂)
    (β : F.obj (I.obj K) ⟶ J.obj (F₂.obj K))
    (hβ : adj.unit.app (I.obj K) ≫ G.map β ≫ θ.app (F₂.obj K) = I.map (adj₂.unit.app K)) :
    adj.unitProjection (I.obj K) ≫ G.map β ≫ θ.app (F₂.obj K) =
      (I.obj K ◁ (G.map (ε J) ≫ θ.app (𝟙_ D₂))) ≫ μ I K (G₂.obj (𝟙_ D₂)) ≫
        I.map (adj₂.unitProjection K) := by
  have hθ := NatTrans.IsMonoidal.tensor (τ := θ) (F₂.obj K) (𝟙_ D₂)
  rw [Functor.LaxMonoidal.comp_μ, Functor.LaxMonoidal.comp_μ] at hθ
  have hθρ := θ.naturality (ρ_ (F₂.obj K)).hom
  dsimp at hθ hθρ
  rw [unitProjection, Category.assoc, Category.assoc, ← G.map_comp_assoc,
    ← rightUnitor_naturality, G.map_comp_assoc, ← μ_natural_left_assoc, ← comp_whiskerRight_assoc,
    Functor.LaxMonoidal.right_unitality J (F₂.obj K), G.map_comp_assoc, G.map_comp_assoc,
    ← μ_natural_right_assoc, hθρ, reassoc_of% hθ, tensorHom_def, Category.assoc,
    whisker_exchange_assoc, ← comp_whiskerRight_assoc, Category.assoc, hβ,
    ← MonoidalCategory.whiskerLeft_comp_assoc, unitProjection, I.map_comp, I.map_comp]
  erw [← μ_natural_left_assoc]
  erw [whisker_exchange_assoc]
  rfl

end Restriction

end CategoryTheory.Adjunction

namespace CategoryTheory.NatTrans.IsMonoidal

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]

/-- A monoidal natural transformation between strong monoidal functors is compatible with the
comparisons `δ` of the oplax monoidal structures. -/
@[reassoc]
lemma δ_comp_tensorHom {F₁ F₂ : C ⥤ D} [F₁.Monoidal] [F₂.Monoidal] (τ : F₁ ⟶ F₂)
    [NatTrans.IsMonoidal τ] (X Y : C) :
    δ F₁ X Y ≫ (τ.app X ⊗ₘ τ.app Y) = τ.app (X ⊗ Y) ≫ δ F₂ X Y := by
  rw [← cancel_epi (μ F₁ X Y), Functor.Monoidal.μ_δ_assoc, NatTrans.IsMonoidal.tensor_assoc,
    Functor.Monoidal.μ_δ, Category.comp_id]

end CategoryTheory.NatTrans.IsMonoidal
