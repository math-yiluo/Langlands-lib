/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.DerivedExactSquare

/-! # Localization formula for a square of exact functors

Source: the universal property of localization and the canonical exact-functor
composition comparisons (Stacks Project, Tags 05S7 and 014F).
(blueprint: lem-weil-pbc-derived-exact-square-factorization).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
  [Abelian C] [Abelian D] [Abelian E] [Abelian F]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [HasDerivedCategory E] [HasDerivedCategory F]
  (R : C ⥤ D) (G : D ⥤ F) (L : C ⥤ E) (S : E ⥤ F)
  [R.Additive] [G.Additive] [L.Additive] [S.Additive]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]

/-- The constructed square is characterized by its ordinary localization square.
Source: the defining factorization equations for exact functors on derived categories.
(blueprint: lem-weil-pbc-derived-exact-square-factorization).

Proof: Postcompose the constructed square with the localization factors for L and S.
The composition factorization cancels the last comparison, and the natural-isomorphism
factorization replaces the middle comparison by the localized ordinary map. The first
inverse-composition comparison cancels using its own factorization equation. -/
theorem mapDerivedCategoryPlusSquareIso_fac (e : R ⋙ G ≅ L ⋙ S)
    (K : HomotopyCategory.Plus C) :
    (mapDerivedCategoryPlusSquareIso R G L S e).hom.app (DerivedCategory.Plus.Qh.obj K) ≫
      S.mapDerivedCategoryPlus.map (L.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
      S.mapDerivedCategoryPlusFactorsh.hom.app (L.mapHomotopyCategoryPlus.obj K) =
    G.mapDerivedCategoryPlus.map (R.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
      G.mapDerivedCategoryPlusFactorsh.hom.app (R.mapHomotopyCategoryPlus.obj K) ≫
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus e.hom).app K) := by
  let : PreservesFiniteLimits (R ⋙ G) := comp_preservesFiniteLimits _ _
  let : PreservesFiniteColimits (R ⋙ G) := comp_preservesFiniteColimits _ _
  let : PreservesFiniteLimits (L ⋙ S) := comp_preservesFiniteLimits _ _
  let : PreservesFiniteColimits (L ⋙ S) := comp_preservesFiniteColimits _ _
  have hc := mapDerivedCategoryPlusCompIso_hom_app_factorsh R G K
  have hi : (mapDerivedCategoryPlusCompIso R G).inv.app (DerivedCategory.Plus.Qh.obj K) ≫
      (R ⋙ G).mapDerivedCategoryPlusFactorsh.hom.app K =
    G.mapDerivedCategoryPlus.map (R.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
      G.mapDerivedCategoryPlusFactorsh.hom.app (R.mapHomotopyCategoryPlus.obj K) := by
    apply (cancel_epi
      ((mapDerivedCategoryPlusCompIso R G).hom.app (DerivedCategory.Plus.Qh.obj K))).mp
    rw [Iso.hom_inv_id_app_assoc]
    exact hc.symm
  simp only [mapDerivedCategoryPlusSquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc]
  rw [mapDerivedCategoryPlusCompIso_hom_app_factorsh,
    mapDerivedCategoryPlusNatIso_hom_app_factorsh]
  rw [← Category.assoc, hi, Category.assoc]

section Composition

variable {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
  [Category C₀] [Category C₁] [Category C₂]
  [Category D₀] [Category D₁] [Category D₂]
  [Abelian C₀] [Abelian C₁] [Abelian C₂]
  [Abelian D₀] [Abelian D₁] [Abelian D₂]
  [HasDerivedCategory C₀] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
  [HasDerivedCategory D₀] [HasDerivedCategory D₁] [HasDerivedCategory D₂]
  (F₀₁ : C₀ ⥤ C₁) (F₁₂ : C₁ ⥤ C₂) (F₀₂ : C₀ ⥤ C₂)
  (G₀₁ : D₀ ⥤ D₁) (G₁₂ : D₁ ⥤ D₂) (G₀₂ : D₀ ⥤ D₂)
  (U₀ : C₀ ⥤ D₀) (U₁ : C₁ ⥤ D₁) (U₂ : C₂ ⥤ D₂)
  [F₀₁.Additive] [F₁₂.Additive] [F₀₂.Additive]
  [G₀₁.Additive] [G₁₂.Additive] [G₀₂.Additive]
  [U₀.Additive] [U₁.Additive] [U₂.Additive]
  [PreservesFiniteLimits F₀₁] [PreservesFiniteColimits F₀₁]
  [PreservesFiniteLimits F₁₂] [PreservesFiniteColimits F₁₂]
  [PreservesFiniteLimits F₀₂] [PreservesFiniteColimits F₀₂]
  [PreservesFiniteLimits G₀₁] [PreservesFiniteColimits G₀₁]
  [PreservesFiniteLimits G₁₂] [PreservesFiniteColimits G₁₂]
  [PreservesFiniteLimits G₀₂] [PreservesFiniteColimits G₀₂]
  [PreservesFiniteLimits U₀] [PreservesFiniteColimits U₀]
  [PreservesFiniteLimits U₁] [PreservesFiniteColimits U₁]
  [PreservesFiniteLimits U₂] [PreservesFiniteColimits U₂]
  [PreservesFiniteLimits (F₀₁ ⋙ F₁₂)] [PreservesFiniteColimits (F₀₁ ⋙ F₁₂)]
  [PreservesFiniteLimits (G₀₁ ⋙ G₁₂)] [PreservesFiniteColimits (G₀₁ ⋙ G₁₂)]

/-- Exact derived square comparisons respect a specified composition identity.
Source: the localization universal property, Stacks Project, Tags 05S7 and 014F.
(blueprint: lem-weil-pbc-derived-exact-square-factorization).

Proof: Form the two natural transformations in the displayed equation and use
localization extensionality for Qh on bounded-below homotopy objects. Postcompose
both sides with the three invertible localization factors for F₀₁, F₁₂ and U₂.
The factorization of the composite comparison cF and naturality of U₂'s factor
transform the left side into the localization of the left ordinary composite,
preceded by the common localization factors for U₀ and G₀₂. On the right, use
naturality of the square comparison for F₁₂ at the F₀₁ factor, then the square
factorization for F₁₂ and F₀₁, then naturality of the G₁₂ factor and the composite
comparison cG. This gives the same common factors followed by the localization
of the right ordinary composite. The assumed equation hq holds degreewise on
complexes, so the localized composites agree. Cancel the three isomorphisms,
apply localization extensionality and evaluate at K. No unit, nonzero-object,
resolution, or preservation-of-injectives assumption is used. -/
theorem mapDerivedCategoryPlusSquareIso_comp
    (q₀₁ : U₀ ⋙ G₀₁ ≅ F₀₁ ⋙ U₁)
    (q₁₂ : U₁ ⋙ G₁₂ ≅ F₁₂ ⋙ U₂)
    (q₀₂ : U₀ ⋙ G₀₂ ≅ F₀₂ ⋙ U₂)
    (cF : F₀₂ ≅ F₀₁ ⋙ F₁₂) (cG : G₀₂ ≅ G₀₁ ⋙ G₁₂)
    (hq : ∀ X : C₀, q₀₂.hom.app X ≫ U₂.map (cF.hom.app X) =
      cG.hom.app (U₀.obj X) ≫ G₁₂.map (q₀₁.hom.app X) ≫ q₁₂.hom.app (F₀₁.obj X))
    (K : DerivedCategory.Plus C₀) :
    (mapDerivedCategoryPlusSquareIso U₀ G₀₂ F₀₂ U₂ q₀₂).hom.app K ≫
      U₂.mapDerivedCategoryPlus.map
        ((mapDerivedCategoryPlusNatIso cF ≪≫
          mapDerivedCategoryPlusCompIso F₀₁ F₁₂).hom.app K) =
    (mapDerivedCategoryPlusNatIso cG ≪≫
        mapDerivedCategoryPlusCompIso G₀₁ G₁₂).hom.app (U₀.mapDerivedCategoryPlus.obj K) ≫
      G₁₂.mapDerivedCategoryPlus.map
        ((mapDerivedCategoryPlusSquareIso U₀ G₀₁ F₀₁ U₁ q₀₁).hom.app K) ≫
      (mapDerivedCategoryPlusSquareIso U₁ G₁₂ F₁₂ U₂ q₁₂).hom.app
        (F₀₁.mapDerivedCategoryPlus.obj K) := by
  -- The ordinary identity descends degreewise to the homotopy categories.
  have hqh (X : HomotopyCategory.Plus C₀) :
      (NatTrans.mapHomotopyCategoryPlus q₀₂.hom).app X ≫
          U₂.mapHomotopyCategoryPlus.map
            ((NatTrans.mapHomotopyCategoryPlus cF.hom).app X) =
        (NatTrans.mapHomotopyCategoryPlus cG.hom).app
            (U₀.mapHomotopyCategoryPlus.obj X) ≫
          G₁₂.mapHomotopyCategoryPlus.map
            ((NatTrans.mapHomotopyCategoryPlus q₀₁.hom).app X) ≫
          (NatTrans.mapHomotopyCategoryPlus q₁₂.hom).app
            (F₀₁.mapHomotopyCategoryPlus.obj X) := by
    apply (HomotopyCategory.Plus.ι D₂).map_injective
    obtain ⟨⟨X⟩, hX⟩ := X
    change (HomotopyCategory.quotient D₂ (ComplexShape.up ℤ)).map _ ≫
        (HomotopyCategory.quotient D₂ (ComplexShape.up ℤ)).map _ =
      (HomotopyCategory.quotient D₂ (ComplexShape.up ℤ)).map _ ≫
        (HomotopyCategory.quotient D₂ (ComplexShape.up ℤ)).map _ ≫
        (HomotopyCategory.quotient D₂ (ComplexShape.up ℤ)).map _
    simp only [← Functor.map_comp]
    congr 1
    ext n
    exact hq (X.X n)
  let a := mapDerivedCategoryPlusSquareIso U₀ G₀₂ F₀₂ U₂ q₀₂
  let b := mapDerivedCategoryPlusSquareIso U₀ G₀₁ F₀₁ U₁ q₀₁
  let c := mapDerivedCategoryPlusSquareIso U₁ G₁₂ F₁₂ U₂ q₁₂
  let dF := mapDerivedCategoryPlusNatIso cF ≪≫ mapDerivedCategoryPlusCompIso F₀₁ F₁₂
  let dG := mapDerivedCategoryPlusNatIso cG ≪≫ mapDerivedCategoryPlusCompIso G₀₁ G₁₂
  let τ₁ := a.hom ≫ whiskerRight dF.hom U₂.mapDerivedCategoryPlus
  let τ₂ := whiskerLeft U₀.mapDerivedCategoryPlus dG.hom ≫
    (associator _ _ _).inv ≫ whiskerRight b.hom G₁₂.mapDerivedCategoryPlus ≫
    (associator _ _ _).hom ≫ whiskerLeft F₀₁.mapDerivedCategoryPlus c.hom ≫
    (associator _ _ _).inv
  -- Localization detects equality; the common factors below are invertible.
  have ht : τ₁ = τ₂ := by
    apply Localization.natTrans_ext DerivedCategory.Plus.Qh
      (HomotopyCategory.Plus.quasiIso C₀)
    intro X
    dsimp only [τ₁, τ₂, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
      associator_hom_app, associator_inv_app]
    simp only [Category.id_comp, Category.comp_id]
    apply (cancel_mono
      (U₂.mapDerivedCategoryPlus.map
        (F₁₂.mapDerivedCategoryPlus.map (F₀₁.mapDerivedCategoryPlusFactorsh.hom.app X)) ≫
       U₂.mapDerivedCategoryPlus.map
        (F₁₂.mapDerivedCategoryPlusFactorsh.hom.app (F₀₁.mapHomotopyCategoryPlus.obj X)) ≫
       U₂.mapDerivedCategoryPlusFactorsh.hom.app
        (F₁₂.mapHomotopyCategoryPlus.obj (F₀₁.mapHomotopyCategoryPlus.obj X)))).mp
    -- Factor the two composition comparisons through Qh.
    have hdF : dF.hom.app (DerivedCategory.Plus.Qh.obj X) ≫
        F₁₂.mapDerivedCategoryPlus.map (F₀₁.mapDerivedCategoryPlusFactorsh.hom.app X) ≫
        F₁₂.mapDerivedCategoryPlusFactorsh.hom.app (F₀₁.mapHomotopyCategoryPlus.obj X) =
      F₀₂.mapDerivedCategoryPlusFactorsh.hom.app X ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus cF.hom).app X) := by
      dsimp only [dF, Iso.trans_hom, NatTrans.comp_app]
      rw [Category.assoc, mapDerivedCategoryPlusCompIso_hom_app_factorsh,
        mapDerivedCategoryPlusNatIso_hom_app_factorsh]
    have hdG : dG.hom.app (DerivedCategory.Plus.Qh.obj
          (U₀.mapHomotopyCategoryPlus.obj X)) ≫
        G₁₂.mapDerivedCategoryPlus.map (G₀₁.mapDerivedCategoryPlusFactorsh.hom.app
          (U₀.mapHomotopyCategoryPlus.obj X)) ≫
        G₁₂.mapDerivedCategoryPlusFactorsh.hom.app
          (G₀₁.mapHomotopyCategoryPlus.obj (U₀.mapHomotopyCategoryPlus.obj X)) =
      G₀₂.mapDerivedCategoryPlusFactorsh.hom.app (U₀.mapHomotopyCategoryPlus.obj X) ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus cG.hom).app
          (U₀.mapHomotopyCategoryPlus.obj X)) := by
      dsimp only [dG, Iso.trans_hom, NatTrans.comp_app]
      rw [Category.assoc, mapDerivedCategoryPlusCompIso_hom_app_factorsh,
        mapDerivedCategoryPlusNatIso_hom_app_factorsh]
    -- Normalize the left pasted square using the factorization of q₀₂.
    have hl : a.hom.app (DerivedCategory.Plus.Qh.obj X) ≫
        U₂.mapDerivedCategoryPlus.map (dF.hom.app (DerivedCategory.Plus.Qh.obj X)) ≫
        U₂.mapDerivedCategoryPlus.map
          (F₁₂.mapDerivedCategoryPlus.map (F₀₁.mapDerivedCategoryPlusFactorsh.hom.app X)) ≫
        U₂.mapDerivedCategoryPlus.map (F₁₂.mapDerivedCategoryPlusFactorsh.hom.app
          (F₀₁.mapHomotopyCategoryPlus.obj X)) ≫
        U₂.mapDerivedCategoryPlusFactorsh.hom.app
          (F₁₂.mapHomotopyCategoryPlus.obj (F₀₁.mapHomotopyCategoryPlus.obj X)) =
      G₀₂.mapDerivedCategoryPlus.map (U₀.mapDerivedCategoryPlusFactorsh.hom.app X) ≫
        G₀₂.mapDerivedCategoryPlusFactorsh.hom.app (U₀.mapHomotopyCategoryPlus.obj X) ≫
        DerivedCategory.Plus.Qh.map
          ((NatTrans.mapHomotopyCategoryPlus q₀₂.hom).app X ≫
            U₂.mapHomotopyCategoryPlus.map
              ((NatTrans.mapHomotopyCategoryPlus cF.hom).app X)) := by
      rw [← U₂.mapDerivedCategoryPlus.map_comp_assoc,
        ← U₂.mapDerivedCategoryPlus.map_comp_assoc, Category.assoc, hdF,
        U₂.mapDerivedCategoryPlus.map_comp_assoc]
      erw [U₂.mapDerivedCategoryPlusFactorsh.hom.naturality]
      simp only [Functor.comp_map]
      erw [reassoc_of% (mapDerivedCategoryPlusSquareIso_fac U₀ G₀₂ F₀₂ U₂ q₀₂ X)]
      simp only [Functor.map_comp]
    simp only [Category.assoc]
    rw [hl]
    -- Normalize the right pasting, moving factors across the natural comparisons.
    have hn := c.hom.naturality (F₀₁.mapDerivedCategoryPlusFactorsh.hom.app X)
    dsimp only [Functor.comp_map] at hn
    erw [← reassoc_of% hn]
    erw [mapDerivedCategoryPlusSquareIso_fac U₁ G₁₂ F₁₂ U₂ q₁₂
      (F₀₁.mapHomotopyCategoryPlus.obj X)]
    rw [← G₁₂.mapDerivedCategoryPlus.map_comp_assoc,
      ← G₁₂.mapDerivedCategoryPlus.map_comp_assoc, Category.assoc]
    erw [mapDerivedCategoryPlusSquareIso_fac U₀ G₀₁ F₀₁ U₁ q₀₁ X]
    simp only [Functor.map_comp, Category.assoc]
    erw [reassoc_of% (G₁₂.mapDerivedCategoryPlusFactorsh.hom.naturality
      ((NatTrans.mapHomotopyCategoryPlus q₀₁.hom).app X))]
    have hnG := dG.hom.naturality (U₀.mapDerivedCategoryPlusFactorsh.hom.app X)
    dsimp only [Functor.comp_map] at hnG
    erw [← reassoc_of% hnG, reassoc_of% hdG]
    simpa only [Functor.map_comp, Category.assoc] using congrArg
      (fun f ↦ G₀₂.mapDerivedCategoryPlus.map (U₀.mapDerivedCategoryPlusFactorsh.hom.app X) ≫
        G₀₂.mapDerivedCategoryPlusFactorsh.hom.app (U₀.mapHomotopyCategoryPlus.obj X) ≫
        DerivedCategory.Plus.Qh.map f) (hqh X)
  simpa only [τ₁, τ₂, a, b, c, dF, dG, NatTrans.comp_app, whiskerLeft_app,
    whiskerRight_app, associator_hom_app, associator_inv_app, Category.id_comp,
    Category.comp_id] using NatTrans.congr_app ht K

end Composition

end CategoryTheory.Functor
