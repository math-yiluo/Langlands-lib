/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MateCounit

/-!
# The isomorphism of composites of left derived functors and the counits

For exact functors with `τ : G₁ ⋙ G₂ ≅ F₁ ⋙ F₂`, the isomorphism
`Functor.leftDerivedFunctorCompNatIso : LG₁ ⋙ LG₂ ≅ LF₁ ⋙ LF₂` is compatible with the composite
counits: on the image of a complex it is induced by `τ` on homotopy categories
(`Functor.leftDerivedFunctorCompNatIso_hom_app_comp_counit`), through the isomorphism
`Functor.mapHomotopyCategoryCompNatIso` of functors between homotopy categories induced by `τ`.
-/

@[expose] public section

universe u u₁ u₂ u₃ u₄

open CategoryTheory Limits

namespace CategoryTheory.Functor

section HomotopyCategory

variable {ι : Type*} {V₁ V₂ V₃ V₄ : Type*} [Category* V₁] [Category* V₂] [Category* V₃]
  [Category* V₄] [Preadditive V₁] [Preadditive V₂] [Preadditive V₃] [Preadditive V₄]
  {F₁ : V₁ ⥤ V₂} {F₂ : V₂ ⥤ V₄} {G₁ : V₁ ⥤ V₃} {G₂ : V₃ ⥤ V₄}
  [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]

/-- The isomorphism `G₁ ⋙ G₂ ≅ F₁ ⋙ F₂` of functors between homotopy categories induced by an
isomorphism `τ : G₁ ⋙ G₂ ≅ F₁ ⋙ F₂` of additive functors. -/
noncomputable def mapHomotopyCategoryCompNatIso (τ : G₁ ⋙ G₂ ≅ F₁ ⋙ F₂) (c : ComplexShape ι) :
    G₁.mapHomotopyCategory c ⋙ G₂.mapHomotopyCategory c ≅
      F₁.mapHomotopyCategory c ⋙ F₂.mapHomotopyCategory c :=
  mapHomotopyCategoryCompIso (Iso.refl _) c ≪≫
    { hom := NatTrans.mapHomotopyCategory τ.hom c
      inv := NatTrans.mapHomotopyCategory τ.inv c
      hom_inv_id := by simp [← NatTrans.mapHomotopyCategory_comp]
      inv_hom_id := by simp [← NatTrans.mapHomotopyCategory_comp] } ≪≫
    (mapHomotopyCategoryCompIso (Iso.refl _) c).symm

/-- The components of `CategoryTheory.Functor.mapHomotopyCategoryCompNatIso`. -/
lemma mapHomotopyCategoryCompNatIso_hom (τ : G₁ ⋙ G₂ ≅ F₁ ⋙ F₂) (c : ComplexShape ι) :
    (mapHomotopyCategoryCompNatIso τ c).hom =
      ((mapHomotopyCategoryCompIso (Iso.refl (G₁ ⋙ G₂)) c).hom ≫
        NatTrans.mapHomotopyCategory τ.hom c) ≫
        (mapHomotopyCategoryCompIso (Iso.refl (F₁ ⋙ F₂)) c).inv := by
  simp [mapHomotopyCategoryCompNatIso]

end HomotopyCategory

open Abelian

variable {C : Type u₁} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [HasFunctorialFlatResolution D]
  {E : Type u₃} [Category.{u + 1} E] [Abelian E] [IsGrothendieckAbelian.{u + 1} E]
  {D' : Type u₄} [Category.{u + 1} D'] [Abelian D'] [IsGrothendieckAbelian.{u + 1} D']
  [MonoidalCategory D'] [MonoidalPreadditive D'] [MonoidalClosed D'] [BraidedCategory D']
  [HasFunctorialFlatResolution D']
  (F₁ : C ⥤ D) [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  (F₂ : D ⥤ E) [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  (G₁ : C ⥤ D') [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  (G₂ : D' ⥤ E) [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- The isomorphism `LG₁ ⋙ LG₂ ≅ LF₁ ⋙ LF₂` induced by `τ : G₁ ⋙ G₂ ≅ F₁ ⋙ F₂` is compatible
with the composite counits: on the image of a complex `K`, it is induced by `τ` on homotopy
categories, that is, the following square commutes.
```
LG₂ (LG₁ K) ──(leftDerivedFunctorCompNatIso τ).hom──▶ LF₂ (LF₁ K)
     │                                                     │
  LG₂ ε, ε                                              LF₂ ε, ε
     ▼                                                     ▼
G₂ (G₁ K) ─────────────────── τ.hom ─────────────────▶ F₂ (F₁ K)
```
-/
lemma leftDerivedFunctorCompNatIso_hom_app_comp_counit (τ : G₁ ⋙ G₂ ≅ F₁ ⋙ F₂)
    (K : HomotopyCategory C (.up ℤ)) :
    (leftDerivedFunctorCompNatIso F₁ F₂ G₁ G₂ τ).hom.app (DerivedCategory.Qh.obj K) ≫
        F₂.leftDerivedFunctor.map (F₁.leftDerivedFunctorCounit.app K) ≫
        F₂.leftDerivedFunctorCounit.app ((F₁.mapHomotopyCategory (.up ℤ)).obj K) =
      G₂.leftDerivedFunctor.map (G₁.leftDerivedFunctorCounit.app K) ≫
        G₂.leftDerivedFunctorCounit.app ((G₁.mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((mapHomotopyCategoryCompIso (Iso.refl (G₁ ⋙ G₂)) (.up ℤ)).hom.app K ≫
            (NatTrans.mapHomotopyCategory τ.hom (.up ℤ)).app K ≫
            (mapHomotopyCategoryCompIso (Iso.refl (F₁ ⋙ F₂)) (.up ℤ)).inv.app K) := by
  rw [mapHomotopyCategoryCompIso_refl_hom_app, mapHomotopyCategoryCompIso_refl_inv_app]
  erw [Category.id_comp, Category.comp_id]
  simp only [leftDerivedFunctorCompNatIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc]
  have k : (G₁.leftDerivedFunctorCompIso G₂).inv.app (DerivedCategory.Qh.obj K) ≫
      (G₁ ⋙ G₂).leftDerivedFunctorCounit.app K =
        G₂.leftDerivedFunctor.map (G₁.leftDerivedFunctorCounit.app K) ≫
          G₂.leftDerivedFunctorCounit.app ((G₁.mapHomotopyCategory _).obj K) := by
    rw [← leftDerivedFunctorCompIso_hom_app_comp_counit, Iso.inv_hom_id_app_assoc]
  rw [leftDerivedFunctorCompIso_hom_app_comp_counit, leftDerivedFunctorNatIso_hom_app_comp_counit,
    reassoc_of% k]

end CategoryTheory.Functor
