/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategorySquarePasting

/-!
# Exact derivation preserves commutative cubes of comparison squares

Compatibilities of `CategoryTheory.Functor.mapDerivedCategorySquareIso` with vertical
composition and whiskering, and the preservation of commutative cubes of comparison squares
(`CategoryTheory.Functor.mapDerivedCategorySquareIso_cube`).
-/

@[expose] public section

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace CategoryTheory.Functor

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

section SquareIso

variable {A B B' B'' E : Type*} [Category A] [Category B] [Category B'] [Category B'']
  [Category E]
  [Abelian A] [Abelian B] [Abelian B'] [Abelian B''] [Abelian E]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory B']
  [HasDerivedCategory B''] [HasDerivedCategory E]

/-- The derived comparison of a vertical composite of two squares with the same edges is the
composite of the derived comparisons. -/
lemma mapDerivedCategorySquareIso_trans_hom {F₁ : A ⥤ B} {F₂ : B ⥤ E} {H₁ : A ⥤ B'}
    {H₂ : B' ⥤ E} {G₁ : A ⥤ B''} {G₂ : B'' ⥤ E}
    [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [H₁.Additive] [PreservesFiniteLimits H₁] [PreservesFiniteColimits H₁]
    [H₂.Additive] [PreservesFiniteLimits H₂] [PreservesFiniteColimits H₂]
    [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (x : F₁ ⋙ F₂ ≅ H₁ ⋙ H₂) (y : H₁ ⋙ H₂ ≅ G₁ ⋙ G₂) :
    (mapDerivedCategorySquareIso (x ≪≫ y)).hom =
      (mapDerivedCategorySquareIso x).hom ≫ (mapDerivedCategorySquareIso y).hom := by
  simp [mapDerivedCategoryNatIso_trans]

/-- The derived comparison of a left whiskered isomorphism is the whiskered derived
isomorphism. -/
lemma mapDerivedCategorySquareIso_isoWhiskerLeft_hom (F : A ⥤ B) {G G' : B ⥤ E}
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [G'.Additive] [PreservesFiniteLimits G'] [PreservesFiniteColimits G'] (e : G ≅ G') :
    (mapDerivedCategorySquareIso (F₁ := F) (F₂ := G) (G₁ := F) (G₂ := G')
      (isoWhiskerLeft F e)).hom = whiskerLeft D(F) (mapDerivedCategoryNatIso e).hom := by
  simp only [mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom]
  rw [mapDerivedCategoryNatIso_isoWhiskerLeft, Iso.hom_inv_id_assoc]

/-- The derived comparison of a right whiskered isomorphism is the whiskered derived
isomorphism. -/
lemma mapDerivedCategorySquareIso_isoWhiskerRight_hom {F F' : A ⥤ B} (G : B ⥤ E)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F'.Additive] [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ F') :
    (mapDerivedCategorySquareIso (F₁ := F) (F₂ := G) (G₁ := F') (G₂ := G)
      (isoWhiskerRight e G)).hom = whiskerRight (mapDerivedCategoryNatIso e).hom D(G) := by
  simp only [mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom]
  rw [mapDerivedCategoryNatIso_isoWhiskerRight, Iso.hom_inv_id_assoc]

end SquareIso

section Cube

variable {A B B' C P Q Q' R : Type*}
  [Category A] [Category B] [Category B'] [Category C]
  [Category P] [Category Q] [Category Q'] [Category R]
  [Abelian A] [Abelian B] [Abelian B'] [Abelian C]
  [Abelian P] [Abelian Q] [Abelian Q'] [Abelian R]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory B']
  [HasDerivedCategory C] [HasDerivedCategory P] [HasDerivedCategory Q]
  [HasDerivedCategory Q'] [HasDerivedCategory R]
  {L₁ : A ⥤ B} {L₂ : B ⥤ C} {L₁' : A ⥤ B'} {L₂' : B' ⥤ C}
  {K₀ : A ⥤ P} {K₁ : B ⥤ Q} {K₁' : B' ⥤ Q'} {K₂ : C ⥤ R}
  {R₁ : P ⥤ Q} {R₂ : Q ⥤ R} {R₁' : P ⥤ Q'} {R₂' : Q' ⥤ R}
  [L₁.Additive] [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
  [L₂.Additive] [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
  [L₁'.Additive] [PreservesFiniteLimits L₁'] [PreservesFiniteColimits L₁']
  [L₂'.Additive] [PreservesFiniteLimits L₂'] [PreservesFiniteColimits L₂']
  [K₀.Additive] [PreservesFiniteLimits K₀] [PreservesFiniteColimits K₀]
  [K₁.Additive] [PreservesFiniteLimits K₁] [PreservesFiniteColimits K₁]
  [K₁'.Additive] [PreservesFiniteLimits K₁'] [PreservesFiniteColimits K₁']
  [K₂.Additive] [PreservesFiniteLimits K₂] [PreservesFiniteColimits K₂]
  [R₁.Additive] [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
  [R₂.Additive] [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
  [R₁'.Additive] [PreservesFiniteLimits R₁'] [PreservesFiniteColimits R₁']
  [R₂'.Additive] [PreservesFiniteLimits R₂'] [PreservesFiniteColimits R₂']

/-- Exact derivation preserves commutative cubes of comparison squares: if the cube
```
        L₁       L₂                 L₁'      L₂'
   A ────▶ B ────▶ C           A ────▶ B' ────▶ C
   │       │       │           │       │        │
 K₀│  c₁   │K₁ c₂  │K₂       K₀│  c₁'  │K₁' c₂' │K₂
   ▼       ▼       ▼           ▼       ▼        ▼
   P ────▶ Q ────▶ R           P ────▶ Q' ────▶ R
        R₁       R₂                 R₁'      R₂'
```
with top face `se` and bottom face `sp` commutes, that is, the two pasted isomorphisms
`(L₁ ⋙ L₂) ⋙ K₂ ≅ K₀ ⋙ (R₁' ⋙ R₂')` agree, then so does the cube of the derived comparisons
`mapDerivedCategorySquareIso` on unbounded derived categories. -/
theorem mapDerivedCategorySquareIso_cube (c₂ : L₂ ⋙ K₂ ≅ K₁ ⋙ R₂)
    (c₁ : L₁ ⋙ K₁ ≅ K₀ ⋙ R₁) (c₂' : L₂' ⋙ K₂ ≅ K₁' ⋙ R₂') (c₁' : L₁' ⋙ K₁' ≅ K₀ ⋙ R₁')
    (se : L₁ ⋙ L₂ ≅ L₁' ⋙ L₂') (sp : R₁ ⋙ R₂ ≅ R₁' ⋙ R₂')
    (h : isoWhiskerLeft L₁ c₂ ≪≫ isoWhiskerRight c₁ R₂ ≪≫ isoWhiskerLeft K₀ sp =
      isoWhiskerRight se K₂ ≪≫ isoWhiskerLeft L₁' c₂' ≪≫ isoWhiskerRight c₁' R₂')
    (M : DerivedCategory A) :
    (mapDerivedCategorySquareIso c₂).hom.app (D(L₁).obj M) ≫
        D(R₂).map ((mapDerivedCategorySquareIso c₁).hom.app M) ≫
        (mapDerivedCategorySquareIso sp).hom.app (D(K₀).obj M) =
      D(K₂).map ((mapDerivedCategorySquareIso se).hom.app M) ≫
        (mapDerivedCategorySquareIso c₂').hom.app (D(L₁').obj M) ≫
        D(R₂').map ((mapDerivedCategorySquareIso c₁').hom.app M) := by
  have hpath : (isoWhiskerLeft L₁ c₂ ≪≫ isoWhiskerRight c₁ R₂) ≪≫ isoWhiskerLeft K₀ sp =
      isoWhiskerRight se K₂ ≪≫ (isoWhiskerLeft L₁' c₂' ≪≫ isoWhiskerRight c₁' R₂') :=
    (Iso.trans_assoc _ _ _).trans h
  have hS := congrArg (fun e ↦ (mapDerivedCategorySquareIso (F₁ := L₁ ⋙ L₂) (F₂ := K₂)
    (G₁ := K₀) (G₂ := R₁' ⋙ R₂') e).hom.app M) hpath
  rw [mapDerivedCategorySquareIso_trans_hom (H₁ := K₀) (H₂ := R₁ ⋙ R₂),
    mapDerivedCategorySquareIso_trans_hom (H₁ := L₁' ⋙ L₂') (H₂ := K₂),
    mapDerivedCategorySquareIso_paste, mapDerivedCategorySquareIso_paste,
    mapDerivedCategorySquareIso_isoWhiskerLeft_hom,
    mapDerivedCategorySquareIso_isoWhiskerRight_hom] at hS
  have hS' := D(K₂).map ((mapDerivedCategoryCompIso L₁ L₂).hom.app M) ≫= hS =≫
    (mapDerivedCategoryCompIso R₁' R₂').inv.app (D(K₀).obj M)
  simp only [NatTrans.comp_app, isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app,
    whiskerRight_app, Iso.symm_hom, Category.assoc] at hS'
  simp only [mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.map_comp, Category.assoc] at hS' ⊢
  rw [← Functor.map_comp_assoc D(K₂) ((mapDerivedCategoryCompIso L₁ L₂).hom.app M)
    ((mapDerivedCategoryCompIso L₁ L₂).inv.app M), Iso.hom_inv_id_app, Functor.map_id,
    Category.id_comp] at hS'
  simpa only [Iso.hom_inv_id_app, Functor.comp_obj, Category.comp_id] using hS'

end Cube

end CategoryTheory.Functor
