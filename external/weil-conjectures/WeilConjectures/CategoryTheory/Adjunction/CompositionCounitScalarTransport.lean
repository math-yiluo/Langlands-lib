/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Transport of a composite counit equation through scalar comparisons

Source: sk-prop-sp-composition.proof.md, inversion of ell and coefficient descent
(blueprint: lem-pur-composition-counit-scalar-transport).
-/

@[expose] public section
set_option autoImplicit false
open CategoryTheory
namespace CategoryTheory.Adjunction

/-- Compatible invertible source and support comparisons transport a composite
counit equation to a scalar image. This is a categorical pasting assertion; it
assumes neither faithfulness nor essential surjectivity of scalar extension.

Source: sk-prop-sp-composition.proof.md, coefficient passage
(blueprint: lem-pur-composition-counit-scalar-transport).

Proof. Map the given equality through UZ. Naturality of the support comparisons,
the three scalar counit equations, and the source-composition square identify
its two sides with a common invertible prefix followed by the desired two
composites. Cancel that prefix. This reuses the proved scalarComposition argument
of FieldCompositionTraceTransport, with no finite-field indices or purity-family
choices in the statement. -/
theorem composition_counit_of_scalar
    {X Y Z X' Y' Z' : Type*}
    [Category X] [Category Y] [Category Z]
    [Category X'] [Category Y'] [Category Z']
    {F : X ⥤ Y} {G : Y ⥤ Z} {H : X ⥤ Z}
    {J : Y ⥤ X} {K : Z ⥤ Y} {L : Z ⥤ X}
    {F' : X' ⥤ Y'} {G' : Y' ⥤ Z'} {H' : X' ⥤ Z'}
    {J' : Y' ⥤ X'} {K' : Z' ⥤ Y'} {L' : Z' ⥤ X'}
    (UX : X ⥤ X') (UY : Y ⥤ Y') (UZ : Z ⥤ Z')
    (α : F ⋙ G ≅ H) (α' : F' ⋙ G' ≅ H')
    (σ : L ≅ K ⋙ J) (σ' : L' ≅ K' ⋙ J')
    (bF : F ⋙ UY ≅ UX ⋙ F') (bG : G ⋙ UZ ≅ UY ⋙ G')
    (bH : H ⋙ UZ ≅ UX ⋙ H')
    (aF : J ⋙ UX ≅ UY ⋙ J') (aG : K ⋙ UY ≅ UZ ⋙ K')
    (aH : L ⋙ UX ≅ UZ ⋙ L')
    (tF : J ⋙ F ⟶ 𝟭 Y) (tG : K ⋙ G ⟶ 𝟭 Z) (tH : L ⋙ H ⟶ 𝟭 Z)
    (tF' : J' ⋙ F' ⟶ 𝟭 Y') (tG' : K' ⋙ G' ⟶ 𝟭 Z')
    (tH' : L' ⋙ H' ⟶ 𝟭 Z')
    (hb : ∀ M, UZ.map (α.hom.app M) ≫ bH.hom.app M =
      bG.hom.app (F.obj M) ≫ G'.map (bF.hom.app M) ≫ α'.hom.app (UX.obj M))
    (ha : ∀ N, UX.map (σ.hom.app N) ≫ aF.hom.app (K.obj N) ≫
      J'.map (aG.hom.app N) = aH.hom.app N ≫ σ'.hom.app (UZ.obj N))
    (hf : ∀ M, UY.map (tF.app M) = bF.hom.app (J.obj M) ≫
      F'.map (aF.hom.app M) ≫ tF'.app (UY.obj M))
    (hg : ∀ N, UZ.map (tG.app N) = bG.hom.app (K.obj N) ≫
      G'.map (aG.hom.app N) ≫ tG'.app (UZ.obj N))
    (hh : ∀ N, UZ.map (tH.app N) = bH.hom.app (L.obj N) ≫
      H'.map (aH.hom.app N) ≫ tH'.app (UZ.obj N))
    (N : Z)
    (h : α.hom.app (L.obj N) ≫ tH.app N =
      G.map (F.map (σ.hom.app N)) ≫ G.map (tF.app (K.obj N)) ≫ tG.app N) :
    α'.hom.app (L'.obj (UZ.obj N)) ≫ tH'.app (UZ.obj N) =
      G'.map (F'.map (σ'.hom.app (UZ.obj N))) ≫
        G'.map (tF'.app (K'.obj (UZ.obj N))) ≫ tG'.app (UZ.obj N) := by
  have left : UZ.map (α.hom.app (L.obj N) ≫ tH.app N) =
      (bG.hom.app (F.obj (L.obj N)) ≫ G'.map (bF.hom.app (L.obj N)) ≫
        G'.map (F'.map (aH.hom.app N))) ≫
        (α'.hom.app (L'.obj (UZ.obj N)) ≫ tH'.app (UZ.obj N)) := by
    simp only [Functor.map_comp, hh, ← Category.assoc]
    rw [hb]
    simp only [Category.assoc]
    rw [← α'.hom.naturality_assoc]
    rfl
  have right : UZ.map
      (G.map (F.map (σ.hom.app N)) ≫ G.map (tF.app (K.obj N)) ≫ tG.app N) =
      (bG.hom.app (F.obj (L.obj N)) ≫ G'.map (bF.hom.app (L.obj N)) ≫
        G'.map (F'.map (aH.hom.app N))) ≫
        (G'.map (F'.map (σ'.hom.app (UZ.obj N))) ≫
          G'.map (tF'.app (K'.obj (UZ.obj N))) ≫ tG'.app (UZ.obj N)) := by
    have bg₁ := bG.hom.naturality (tF.app (K.obj N))
    have bg₂ := bG.hom.naturality (F.map (σ.hom.app N))
    have bf := bF.hom.naturality (σ.hom.app N)
    have tf := tF'.naturality (aG.hom.app N)
    simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj, Functor.id_map]
      at bg₁ bg₂ bf tf
    have inner : UY.map (F.map (σ.hom.app N)) ≫
        UY.map (tF.app (K.obj N)) ≫ aG.hom.app N =
        bF.hom.app (L.obj N) ≫ F'.map (aH.hom.app N) ≫
          F'.map (σ'.hom.app (UZ.obj N)) ≫ tF'.app (K'.obj (UZ.obj N)) := by
      rw [hf]
      simp only [Category.assoc]
      rw [reassoc_of% bf, ← tf]
      simp only [← F'.map_comp_assoc]
      rw [ha]
    simp only [Functor.map_comp, hg, Category.assoc]
    rw [reassoc_of% bg₁, reassoc_of% bg₂]
    simp only [← G'.map_comp_assoc]
    rw [inner]
  have eq := (left.symm.trans (congrArg UZ.map h)).trans right
  exact (cancel_epi (bG.hom.app (F.obj (L.obj N)) ≫
    G'.map (bF.hom.app (L.obj N)) ≫ G'.map (F'.map (aH.hom.app N)))).mp eq


end CategoryTheory.Adjunction
