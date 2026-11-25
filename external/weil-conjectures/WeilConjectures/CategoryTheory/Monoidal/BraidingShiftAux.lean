/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Compatibility of a braiding with a functor, abstractly

`CategoryTheory.braiding_hom_comp_aux` is the computation transporting the compatibility of the
braiding of a homotopy category with the shifts to the derived category: all morphisms are
variables and the inputs are the compatibilities of the localization comparison maps with the
shifts and with the braidings.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace CategoryTheory

variable {D : Type*} [Category D] [MonoidalCategory D] [BraidedCategory D] (S : D ⥤ D)

/-- See the module docstring. With `q : Qh(Z⟦y⟧) ≅ (Qh Z)⟦y⟧`, `cL`, `cR` the commutations of
`X ⊗ -` and `- ⊗ X` with `S`, `m`, `n` the comparison maps of the localization and `hL'`, `hR'`
those of the homotopy category, the compatibility of the braiding with `S` follows from that of
the homotopy category. -/
lemma braiding_hom_comp_aux {X Y Y' W₁ W₂ V₁ V₂ T₁ T₂ : D} (q : Y' ⟶ S.obj Y) [IsIso q]
    (cL : X ⊗ S.obj Y ⟶ S.obj (X ⊗ Y)) (cR : S.obj Y ⊗ X ⟶ S.obj (Y ⊗ X))
    (m₁ : X ⊗ Y ⟶ W₁) (n₁ : Y ⊗ X ⟶ V₁) [IsIso n₁] (m₂ : X ⊗ Y' ⟶ W₂) (n₂ : Y' ⊗ X ⟶ V₂)
    (bH₂ : W₂ ⟶ V₂) (hL' : W₂ ⟶ T₁) (hR' : V₂ ⟶ T₂) (qPK : T₁ ⟶ S.obj W₁)
    (qKP : T₂ ⟶ S.obj V₁) (bH₁ : W₁ ⟶ V₁) (bHs : T₁ ⟶ T₂)
    (hL : X ◁ q ≫ cL ≫ S.map m₁ = m₂ ≫ hL' ≫ qPK)
    (hR : q ▷ X ≫ cR ≫ S.map n₁ = n₂ ≫ hR' ≫ qKP)
    (hβ₁ : (β_ X Y').hom ≫ n₂ = m₂ ≫ bH₂) (hβ₂ : (β_ X Y).hom ≫ n₁ = m₁ ≫ bH₁)
    (hH : bH₂ ≫ hR' = hL' ≫ bHs) (hQ : bHs ≫ qKP = qPK ≫ S.map bH₁) :
    (β_ X (S.obj Y)).hom ≫ cR = cL ≫ S.map (β_ X Y).hom := by
  rw [← cancel_epi (X ◁ q), ← cancel_mono (S.map n₁)]
  simp only [Category.assoc]
  rw [BraidedCategory.braiding_naturality_right_assoc, hR, reassoc_of% hβ₁, reassoc_of% hH, hQ,
    ← S.map_comp, hβ₂, S.map_comp, ← reassoc_of% hL]

/-- Transport of the compatibility of the braiding with commutation isomorphisms along an
isomorphism in the second variable. -/
lemma braiding_hom_comp_of_iso_right {X Y Y' : D} (eY : Y ≅ Y') (cL : X ⊗ S.obj Y ⟶ S.obj (X ⊗ Y))
    (cL' : X ⊗ S.obj Y' ⟶ S.obj (X ⊗ Y')) (cR : S.obj Y ⊗ X ⟶ S.obj (Y ⊗ X))
    (cR' : S.obj Y' ⊗ X ⟶ S.obj (Y' ⊗ X))
    (hL : X ◁ S.map eY.hom ≫ cL' = cL ≫ S.map (X ◁ eY.hom))
    (hR : S.map eY.hom ▷ X ≫ cR' = cR ≫ S.map (eY.hom ▷ X))
    (h : (β_ X (S.obj Y')).hom ≫ cR' = cL' ≫ S.map (β_ X Y').hom) :
    (β_ X (S.obj Y)).hom ≫ cR = cL ≫ S.map (β_ X Y).hom := by
  rw [← cancel_mono (S.map (eY.hom ▷ X)), Category.assoc, ← hR,
    ← BraidedCategory.braiding_naturality_right_assoc, h, reassoc_of% hL, Category.assoc,
    ← S.map_comp, ← S.map_comp, BraidedCategory.braiding_naturality_right]

/-- Transport of the compatibility of the braiding with commutation isomorphisms along an
isomorphism in the first variable. -/
lemma braiding_hom_comp_of_iso_left {X X' Y : D} (eX : X ≅ X') (cL : X ⊗ S.obj Y ⟶ S.obj (X ⊗ Y))
    (cL' : X' ⊗ S.obj Y ⟶ S.obj (X' ⊗ Y)) (cR : S.obj Y ⊗ X ⟶ S.obj (Y ⊗ X))
    (cR' : S.obj Y ⊗ X' ⟶ S.obj (Y ⊗ X'))
    (hL : eX.hom ▷ S.obj Y ≫ cL' = cL ≫ S.map (eX.hom ▷ Y))
    (hR : S.obj Y ◁ eX.hom ≫ cR' = cR ≫ S.map (Y ◁ eX.hom))
    (h : (β_ X' (S.obj Y)).hom ≫ cR' = cL' ≫ S.map (β_ X' Y).hom) :
    (β_ X (S.obj Y)).hom ≫ cR = cL ≫ S.map (β_ X Y).hom := by
  rw [← cancel_mono (S.map (Y ◁ eX.hom)), Category.assoc, ← hR,
    ← BraidedCategory.braiding_naturality_left_assoc, h, reassoc_of% hL, Category.assoc,
    ← S.map_comp, ← S.map_comp, BraidedCategory.braiding_naturality_left]

end CategoryTheory
