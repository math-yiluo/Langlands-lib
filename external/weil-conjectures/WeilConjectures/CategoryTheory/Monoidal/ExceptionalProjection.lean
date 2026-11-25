/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Monoidal.Multifunctor
public import Mathlib.CategoryTheory.Monoidal.Subcategory

/-!

# The exceptional projection morphism of a factorization

Let `C`, `E` and `D` be monoidal categories, and let
```
J : C ⥤ E,   G : E ⥤ D,   Lg : D ⥤ E,   Li : E ⥤ C,   Lf : D ⥤ C
```
be functors with an isomorphism `e : Lf ≅ Lg ⋙ Li`. In the application `f = g ∘ i` is a
compactification of a morphism of schemes, with `i` an open immersion and `g` proper, `J = i_!`
is the extension by zero, `G = Rg_*`, and `Lg`, `Li`, `Lf` are the derived pullbacks, so that
`J ⋙ G = Rf_!`. Given

* a projection morphism `π_{A,B} : G A ⊗ B ⟶ G (A ⊗ Lg B)` of bifunctors (the projection
  morphism of `Lg ⊣ G`, `CategoryTheory.Adjunction.rightAdjointProjectionMap`), and
* an isomorphism of bifunctors `q_{M,N} : J (M ⊗ Li N) ⟶ J M ⊗ N` (the projection map of
  `J ⊣ Li`, `CategoryTheory.Adjunction.projectionMap`, an isomorphism for an open immersion),

the *exceptional projection morphism* `(J ⋙ G) K ⊗ B ⟶ (J ⋙ G) (K ⊗ Lf B)` is the composite
```
G (J K) ⊗ B --π--> G (J K ⊗ Lg B) --G (q⁻¹)--> G (J (K ⊗ Li (Lg B))) --G (J (K ◁ e⁻¹))-->
  G (J (K ⊗ Lf B)),
```
natural in both variables (`CategoryTheory.MonoidalCategory.exceptionalProjection`).

-/

@[expose] public section

namespace CategoryTheory.MonoidalCategory

open _root_.CategoryTheory.Functor

section Factorization

variable {C E D : Type*} [Category* C] [Category* E] [Category* D] [MonoidalCategory C]
  [MonoidalCategory E] [MonoidalCategory D] {J : C ⥤ E} {G : E ⥤ D} {Lg : D ⥤ E} {Li : E ⥤ C}
  {Lf : D ⥤ C}
  (π : G ⋙ curriedTensor D ⟶
    (postcompose₂.obj G).obj ((((whiskeringLeft₂ E).obj (𝟭 E)).obj Lg).obj (curriedTensor E)))
  (q : (postcompose₂.obj J).obj ((((whiskeringLeft₂ C).obj (𝟭 C)).obj Li).obj (curriedTensor C)) ⟶
    (((whiskeringLeft₂ E).obj J).obj (𝟭 E)).obj (curriedTensor E)) [IsIso q]
  (e : Lf ≅ Lg ⋙ Li)

/-- The component `(J ⋙ G) K ⊗ B ⟶ (J ⋙ G) (K ⊗ Lf B)` of the exceptional projection morphism:
the composite
```
G (J K) ⊗ B --π--> G (J K ⊗ Lg B) --G (q⁻¹)--> G (J (K ⊗ Li (Lg B))) --G (J (K ◁ e⁻¹))-->
  G (J (K ⊗ Lf B)).
```
-/
noncomputable def exceptionalProjectionApp (K : C) (B : D) :
    (J ⋙ G).obj K ⊗ B ⟶ (J ⋙ G).obj (K ⊗ Lf.obj B) :=
  (π.app (J.obj K)).app B ≫ G.map (((inv q).app K).app (Lg.obj B) ≫ J.map (K ◁ e.inv.app B))

/-- The exceptional projection morphism is natural in its second variable:
```
(J ⋙ G) K ⊗ B -------------> (J ⋙ G) (K ⊗ Lf B)
      |                             |
(J ⋙ G) K ◁ h             (J ⋙ G) (K ◁ Lf h)
      v                             v
(J ⋙ G) K ⊗ B' ------------> (J ⋙ G) (K ⊗ Lf B')
```
-/
@[reassoc]
lemma exceptionalProjectionApp_natural_right (K : C) {B B' : D} (h : B ⟶ B') :
    (J ⋙ G).obj K ◁ h ≫ exceptionalProjectionApp π q e K B' =
      exceptionalProjectionApp π q e K B ≫ (J ⋙ G).map (K ◁ Lf.map h) := by
  have h₁ := (π.app (J.obj K)).naturality h
  have h₂ := ((inv q).app K).naturality (Lg.map h)
  have h₃ := e.inv.naturality h
  dsimp at h₁ h₂ h₃
  simp only [exceptionalProjectionApp, Functor.comp_obj, Functor.comp_map, Category.assoc]
  rw [reassoc_of% h₁]
  simp only [← G.map_comp, Category.assoc]
  rw [reassoc_of% h₂]
  simp only [← J.map_comp, ← MonoidalCategory.whiskerLeft_comp, h₃]

/-- The exceptional projection morphism is natural in its first variable:
```
(J ⋙ G) K ⊗ B -------------> (J ⋙ G) (K ⊗ Lf B)
      |                             |
(J ⋙ G) φ ▷ B             (J ⋙ G) (φ ▷ Lf B)
      v                             v
(J ⋙ G) K' ⊗ B ------------> (J ⋙ G) (K' ⊗ Lf B)
```
-/
@[reassoc]
lemma exceptionalProjectionApp_natural_left {K K' : C} (φ : K ⟶ K') (B : D) :
    (J ⋙ G).map φ ▷ B ≫ exceptionalProjectionApp π q e K' B =
      exceptionalProjectionApp π q e K B ≫ (J ⋙ G).map (φ ▷ Lf.obj B) := by
  have h₁ := NatTrans.congr_app (π.naturality (J.map φ)) B
  have h₂ := NatTrans.congr_app ((inv q).naturality φ) (Lg.obj B)
  dsimp at h₁ h₂
  simp only [exceptionalProjectionApp, Functor.comp_obj, Functor.comp_map, Category.assoc]
  rw [reassoc_of% h₁]
  simp only [← G.map_comp, Category.assoc]
  rw [reassoc_of% h₂]
  simp only [← J.map_comp, whisker_exchange]

/-- The **exceptional projection morphism** `(J ⋙ G) K ⊗ B ⟶ (J ⋙ G) (K ⊗ Lf B)`, as a natural
transformation of bifunctors `C ⥤ D ⥤ D`, with components `exceptionalProjectionApp`. -/
noncomputable def exceptionalProjection :
    curriedTensorInsertFunctor₁ (J ⋙ G) ⟶
      curriedTensorPost (J ⋙ G) ⋙ (whiskeringLeft D C D).obj Lf where
  app K :=
    { app B := exceptionalProjectionApp π q e K B
      naturality _ _ h := exceptionalProjectionApp_natural_right π q e K h }
  naturality _ _ φ := NatTrans.ext <| funext fun B ↦
    exceptionalProjectionApp_natural_left π q e φ B

@[simp]
lemma exceptionalProjection_app_app (K : C) (B : D) :
    ((exceptionalProjection π q e).app K).app B = exceptionalProjectionApp π q e K B :=
  rfl

end Factorization

/-! ### Restriction to full monoidal subcategories -/

section Restriction

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  {PC : ObjectProperty C} {PD : ObjectProperty D} [PC.IsMonoidal] [PD.IsMonoidal]
  {P : C ⥤ D} {F : D ⥤ C} {P₀ : PC.FullSubcategory ⥤ PD.FullSubcategory}
  {F₀ : PD.FullSubcategory ⥤ PC.FullSubcategory}
  (eP : P₀ ⋙ PD.ι ≅ PC.ι ⋙ P) (eF : F₀ ⋙ PC.ι ≅ PD.ι ⋙ F)
  (α : curriedTensorInsertFunctor₁ P ⟶ curriedTensorPost P ⋙ (whiskeringLeft D C D).obj F)

/-- The component `P₀ K ⊗ B ⟶ P₀ (K ⊗ F₀ B)` of the restriction of a morphism of bifunctors
`α : P K ⊗ B ⟶ P (K ⊗ F B)` to full monoidal subcategories, along restrictions `P₀` and `F₀` of
`P` and `F`: the composite
```
P₀ K ⊗ B ≅ P K ⊗ B --α--> P (K ⊗ F B) ≅ P (K ⊗ F₀ B) ≅ P₀ (K ⊗ F₀ B)
```
in the ambient category. -/
def restrictTensorApp (K : PC.FullSubcategory) (B : PD.FullSubcategory) :
    P₀.obj K ⊗ B ⟶ P₀.obj (K ⊗ F₀.obj B) :=
  ObjectProperty.homMk (eP.hom.app K ▷ B.obj ≫ (α.app K.obj).app B.obj ≫
    P.map (K.obj ◁ eF.inv.app B) ≫ eP.inv.app (K ⊗ F₀.obj B))

@[simp]
lemma restrictTensorApp_hom (K : PC.FullSubcategory) (B : PD.FullSubcategory) :
    (restrictTensorApp eP eF α K B).hom = eP.hom.app K ▷ B.obj ≫ (α.app K.obj).app B.obj ≫
      P.map (K.obj ◁ eF.inv.app B) ≫ eP.inv.app (K ⊗ F₀.obj B) :=
  rfl

@[reassoc]
lemma restrictTensorApp_natural_right (K : PC.FullSubcategory) {B B' : PD.FullSubcategory}
    (h : B ⟶ B') :
    P₀.obj K ◁ h ≫ restrictTensorApp eP eF α K B' =
      restrictTensorApp eP eF α K B ≫ P₀.map (K ◁ F₀.map h) := by
  ext
  have h₁ := (α.app K.obj).naturality h.hom
  have h₂ := eP.inv.naturality (K ◁ F₀.map h)
  have h₃ := eF.inv.naturality h
  dsimp at h₁ h₂ h₃ ⊢
  simp only [Category.assoc]
  rw [← h₂, whisker_exchange_assoc, reassoc_of% h₁, ← P.map_comp_assoc, ← P.map_comp_assoc,
    ← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.whiskerLeft_comp, h₃]

@[reassoc]
lemma restrictTensorApp_natural_left {K K' : PC.FullSubcategory} (φ : K ⟶ K')
    (B : PD.FullSubcategory) :
    P₀.map φ ▷ B ≫ restrictTensorApp eP eF α K' B =
      restrictTensorApp eP eF α K B ≫ P₀.map (φ ▷ F₀.obj B) := by
  ext
  have h₁ := NatTrans.congr_app (α.naturality φ.hom) B.obj
  have h₂ := eP.inv.naturality (φ ▷ F₀.obj B)
  have h₃ := eP.hom.naturality φ
  dsimp at h₁ h₂ h₃ ⊢
  simp only [Category.assoc]
  rw [← h₂, ← comp_whiskerRight_assoc, h₃, comp_whiskerRight_assoc, reassoc_of% h₁,
    ← P.map_comp_assoc, ← P.map_comp_assoc, whisker_exchange]

/-- The restriction of a morphism of bifunctors `α : P K ⊗ B ⟶ P (K ⊗ F B)` to full monoidal
subcategories, along restrictions `P₀` and `F₀` of `P` and `F` (with the compatibilities `eP`
and `eF`), with components `restrictTensorApp`. -/
def restrictTensor :
    curriedTensorInsertFunctor₁ P₀ ⟶
      curriedTensorPost P₀ ⋙ (whiskeringLeft PD.FullSubcategory PC.FullSubcategory
        PD.FullSubcategory).obj F₀ where
  app K :=
    { app B := restrictTensorApp eP eF α K B
      naturality _ _ h := restrictTensorApp_natural_right eP eF α K h }
  naturality _ _ φ := NatTrans.ext <| funext fun B ↦ restrictTensorApp_natural_left eP eF α φ B

@[simp]
lemma restrictTensor_app_app (K : PC.FullSubcategory) (B : PD.FullSubcategory) :
    ((restrictTensor eP eF α).app K).app B = restrictTensorApp eP eF α K B :=
  rfl

/-- The components of the restriction are isomorphisms if those of `α` are. -/
instance isIso_restrictTensor_app_app (K : PC.FullSubcategory) (B : PD.FullSubcategory)
    [IsIso ((α.app K.obj).app B.obj)] : IsIso (((restrictTensor eP eF α).app K).app B) := by
  rw [restrictTensor_app_app]
  have : IsIso (PD.ι.map (restrictTensorApp eP eF α K B)) := by
    rw [ObjectProperty.ι_map, restrictTensorApp_hom]
    infer_instance
  exact isIso_of_reflects_iso _ PD.ι

end Restriction

end CategoryTheory.MonoidalCategory
