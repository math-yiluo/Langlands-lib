/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
/-! # Exact derivation preserves pasting of comparison squares -/

@[expose] public section
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace CategoryTheory.Functor
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C] [HasDerivedCategory D]
  (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D)
  [F.Additive] [G.Additive] [H.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

private theorem comp_reassoc :
    (mapDerivedCategoryCompIso (F ⋙ G) H).hom ≫
      (mapDerivedCategoryCompIso F (G ⋙ H)).inv =
    (isoWhiskerRight (mapDerivedCategoryCompIso F G).symm D(H)).hom ≫
      (isoWhiskerLeft D(F) (mapDerivedCategoryCompIso G H)).hom := by
  rw [← Iso.eq_inv_comp, ← Category.assoc, ← Iso.comp_inv_eq]
  exact mapDerivedCategoryCompIso_assoc F G H

private theorem comp_reassoc_inv :
    (mapDerivedCategoryCompIso F (G ⋙ H)).hom ≫
      (mapDerivedCategoryCompIso (F ⋙ G) H).inv =
    (isoWhiskerLeft D(F) (mapDerivedCategoryCompIso G H).symm).hom ≫
      (isoWhiskerRight (mapDerivedCategoryCompIso F G) D(H)).hom := by
  rw [← Iso.eq_inv_comp, ← Category.assoc, ← Iso.comp_inv_eq]
  exact (mapDerivedCategoryCompIso_assoc F G H).symm

section WhiskerEq
variable {A B C : Type*} [Category A] [Category B] [Category C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
private theorem nat_left (F : A ⥤ B) {G G' : B ⥤ C}
    [F.Additive] [G.Additive] [G'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G'] (e : G ≅ G') :
    (mapDerivedCategoryNatIso (isoWhiskerLeft F e)).hom =
      (mapDerivedCategoryCompIso F G).inv ≫
        (isoWhiskerLeft D(F) (mapDerivedCategoryNatIso e)).hom ≫
        (mapDerivedCategoryCompIso F G').hom := by
  rw [← Category.assoc, ← Iso.comp_inv_eq]
  exact mapDerivedCategoryNatIso_isoWhiskerLeft F e
private theorem nat_right {F F' : A ⥤ B} (G : B ⥤ C)
    [F.Additive] [F'.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ F') :
    (mapDerivedCategoryNatIso (isoWhiskerRight e G)).hom =
      (mapDerivedCategoryCompIso F G).inv ≫
        (isoWhiskerRight (mapDerivedCategoryNatIso e) D(G)).hom ≫
        (mapDerivedCategoryCompIso F' G).hom := by
  rw [← Category.assoc, ← Iso.comp_inv_eq]
  exact mapDerivedCategoryNatIso_isoWhiskerRight e G
end WhiskerEq

section Paste
variable {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
  [Category C₀] [Category C₁] [Category C₂] [Category D₀] [Category D₁] [Category D₂]
  [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian D₀] [Abelian D₁] [Abelian D₂]
  [HasDerivedCategory C₀] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
  [HasDerivedCategory D₀] [HasDerivedCategory D₁] [HasDerivedCategory D₂]
  (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (P : D₀ ⥤ D₁) (Q : D₁ ⥤ D₂)
  (E₀ : C₀ ⥤ D₀) (E₁ : C₁ ⥤ D₁) (E₂ : C₂ ⥤ D₂)
  [F.Additive] [G.Additive] [P.Additive] [Q.Additive]
  [E₀.Additive] [E₁.Additive] [E₂.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
  [PreservesFiniteLimits E₀] [PreservesFiniteColimits E₀]
  [PreservesFiniteLimits E₁] [PreservesFiniteColimits E₁]
  [PreservesFiniteLimits E₂] [PreservesFiniteColimits E₂]

/-- Exact derivation takes a pasted comparison to the paste of its derived comparisons.
For the two squares
```
        F         G
   C₀ ────▶ C₁ ────▶ C₂
   │        │        │
 E₀│   α    │E₁  β   │E₂
   ▼        ▼        ▼
   D₀ ────▶ D₁ ────▶ D₂
        P         Q
```
with `α : F ⋙ E₁ ≅ E₀ ⋙ P` and `β : G ⋙ E₂ ≅ E₁ ⋙ Q`, the derived comparison of the outer
square `F ⋙ G`, `P ⋙ Q` is the paste of `D(α)` and `D(β)`, conjugated by the composition
isomorphisms `D(F ⋙ G) ≅ D(F) ⋙ D(G)` and `D(P ⋙ Q) ≅ D(P) ⋙ D(Q)`.
Source: WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate,
composition associativity and whiskering naturality.

Proof. Expand the derived square comparisons. Derivation preserves composition of
natural isomorphisms. Its two whiskering laws express the two derived whiskered maps
using the composition isomorphisms. Apply composition associativity at the three
successive triples to cancel the intermediate composition comparisons. The remaining
factors are precisely the two derived squares and the endpoint composition comparisons.
-/
theorem mapDerivedCategorySquareIso_paste (α : F ⋙ E₁ ≅ E₀ ⋙ P) (β : G ⋙ E₂ ≅ E₁ ⋙ Q) :
    (mapDerivedCategorySquareIso (F₁ := F ⋙ G) (F₂ := E₂)
      (G₁ := E₀) (G₂ := P ⋙ Q) (isoWhiskerLeft F β ≪≫ isoWhiskerRight α Q)).hom =
      (isoWhiskerRight (mapDerivedCategoryCompIso F G).symm D(E₂)).hom ≫
        (isoWhiskerLeft D(F) (mapDerivedCategorySquareIso β)).hom ≫
        (isoWhiskerRight (mapDerivedCategorySquareIso α) D(Q)).hom ≫
        (isoWhiskerLeft D(E₀) (mapDerivedCategoryCompIso P Q)).hom := by
  simp only [mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    mapDerivedCategoryNatIso_trans, nat_left, nat_right, Category.assoc,
    isoWhiskerLeft_hom, isoWhiskerRight_hom,
    whiskerLeft_comp, whiskerRight_comp]
  rw [reassoc_of% (comp_reassoc F G E₂),
    reassoc_of% (comp_reassoc_inv F E₁ Q), comp_reassoc E₀ P Q]
  simp only [isoWhiskerLeft_hom, isoWhiskerRight_hom, Iso.symm_hom]
end Paste

end CategoryTheory.Functor
