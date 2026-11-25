/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
/-! Composition of squares of exact functors after ordinary unbounded localization. -/
@[expose] public section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
private theorem exactSquare_fac
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [Abelian C] [Abelian D] [Abelian E] [Abelian F]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory F]
    {R : C ⥤ D} {G : D ⥤ F} {L : C ⥤ E} {S : E ⥤ F}
    [R.Additive] [G.Additive] [L.Additive] [S.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (e : R ⋙ G ≅ L ⋙ S) (K : CochainComplex C ℤ) :
    (mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj K) ≫
      S.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app K) ≫
      S.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj K) =
    G.mapDerivedCategory.map (R.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K) := by
  have hc := mapDerivedCategoryCompIso_hom_app_factors R G K
  have hi : (mapDerivedCategoryCompIso R G).hom.app (DerivedCategory.Q.obj K) ≫
      (R ⋙ G).mapDerivedCategoryFactors.hom.app K =
    G.mapDerivedCategory.map (R.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj K) := by
    apply (cancel_epi ((mapDerivedCategoryCompIso R G).inv.app (DerivedCategory.Q.obj K))).mp
    rw [Iso.inv_hom_id_app_assoc]
    exact hc.symm
  simp only [mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc]
  rw [mapDerivedCategoryCompIso_hom_app_factors, mapDerivedCategoryNatIso_fac]
  rw [← Category.assoc, hi, Category.assoc]

private theorem square_symm_hom
    {A B B' E : Type*} [Category A] [Category B] [Category B'] [Category E]
    [Abelian A] [Abelian B] [Abelian B'] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory B'] [HasDerivedCategory E]
    {F₁ : A ⥤ B} {F₂ : B ⥤ E} {G₁ : A ⥤ B'} {G₂ : B' ⥤ E}
    [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (q : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) :
    (mapDerivedCategorySquareIso q.symm).hom = (mapDerivedCategorySquareIso q).inv := by
  simp only [mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, mapDerivedCategoryNatIso_symm, Category.assoc]

private theorem square_reverse
    {C D : Type*} [Category C] [Category D] (G : C ⥤ D)
    {X₁ X₂ : C} {Y₀ Y₁ Z₀ : D}
    (q₀ : Y₀ ≅ Z₀) (q₁ : Y₁ ≅ G.obj X₁)
    (q₂ : X₁ ≅ X₂) (a : Y₀ ⟶ Y₁) (b : Z₀ ⟶ G.obj X₂)
    (h : a ≫ q₁.hom ≫ G.map q₂.hom = q₀.hom ≫ b) :
    q₀.inv ≫ a = b ≫ G.map q₂.inv ≫ q₁.inv := by
  have he := congrArg (fun t ↦ q₀.inv ≫ t ≫ G.map q₂.inv ≫ q₁.inv) h
  simpa only [Category.assoc, ← G.map_comp_assoc, ← G.map_comp, Iso.hom_inv_id,
    G.map_id, Category.id_comp, Category.comp_id, Iso.hom_inv_id_assoc,
    Iso.inv_hom_id_assoc] using he

private theorem square_forward
    {C D : Type*} [Category C] [Category D] (G : C ⥤ D)
    {X₁ X₂ : C} {Y₀ Y₁ Z₀ : D}
    (q₀ : Y₀ ≅ Z₀) (q₁ : Y₁ ≅ G.obj X₁)
    (q₂ : X₁ ≅ X₂) (a : Y₀ ⟶ Y₁) (b : Z₀ ⟶ G.obj X₂)
    (h : q₀.inv ≫ a = b ≫ G.map q₂.inv ≫ q₁.inv) :
    a ≫ q₁.hom ≫ G.map q₂.hom = q₀.hom ≫ b := by
  have he := congrArg (fun t ↦ q₀.hom ≫ t ≫ q₁.hom ≫ G.map q₂.hom) h
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
    ← G.map_comp, Iso.inv_hom_id, G.map_id, Category.comp_id] using he

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

private theorem exactSquare_comp_inverse
    (q₀₁ : U₀ ⋙ G₀₁ ≅ F₀₁ ⋙ U₁)
    (q₁₂ : U₁ ⋙ G₁₂ ≅ F₁₂ ⋙ U₂)
    (q₀₂ : U₀ ⋙ G₀₂ ≅ F₀₂ ⋙ U₂)
    (cF : F₀₂ ≅ F₀₁ ⋙ F₁₂) (cG : G₀₂ ≅ G₀₁ ⋙ G₁₂)
    (hq : ∀ X : C₀, q₀₂.hom.app X ≫ U₂.map (cF.hom.app X) =
      cG.hom.app (U₀.obj X) ≫ G₁₂.map (q₀₁.hom.app X) ≫ q₁₂.hom.app (F₀₁.obj X))
    (K : DerivedCategory C₀) :
    (mapDerivedCategorySquareIso q₀₂).hom.app K ≫
      U₂.mapDerivedCategory.map
        ((mapDerivedCategoryNatIso cF ≪≫
          (mapDerivedCategoryCompIso F₀₁ F₁₂).symm).hom.app K) =
    (mapDerivedCategoryNatIso cG ≪≫
        (mapDerivedCategoryCompIso G₀₁ G₁₂).symm).hom.app (U₀.mapDerivedCategory.obj K) ≫
      G₁₂.mapDerivedCategory.map
        ((mapDerivedCategorySquareIso q₀₁).hom.app K) ≫
      (mapDerivedCategorySquareIso q₁₂).hom.app
        (F₀₁.mapDerivedCategory.obj K) := by
  -- The ordinary identity descends degreewise to the homotopy categories.
  have hqh (X : CochainComplex C₀ ℤ) :
      (NatTrans.mapHomologicalComplex q₀₂.hom (.up ℤ)).app X ≫
          (U₂.mapHomologicalComplex (.up ℤ)).map
            ((NatTrans.mapHomologicalComplex cF.hom (.up ℤ)).app X) =
        (NatTrans.mapHomologicalComplex cG.hom (.up ℤ)).app
            ((U₀.mapHomologicalComplex (.up ℤ)).obj X) ≫
          (G₁₂.mapHomologicalComplex (.up ℤ)).map
            ((NatTrans.mapHomologicalComplex q₀₁.hom (.up ℤ)).app X) ≫
          (NatTrans.mapHomologicalComplex q₁₂.hom (.up ℤ)).app
            ((F₀₁.mapHomologicalComplex (.up ℤ)).obj X) := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact hq (X.X n)
  let a := mapDerivedCategorySquareIso q₀₂
  let b := mapDerivedCategorySquareIso q₀₁
  let c := mapDerivedCategorySquareIso q₁₂
  let dF := mapDerivedCategoryNatIso cF ≪≫ (mapDerivedCategoryCompIso F₀₁ F₁₂).symm
  let dG := mapDerivedCategoryNatIso cG ≪≫ (mapDerivedCategoryCompIso G₀₁ G₁₂).symm
  let τ₁ := a.hom ≫ whiskerRight dF.hom U₂.mapDerivedCategory
  let τ₂ := whiskerLeft U₀.mapDerivedCategory dG.hom ≫
    (associator _ _ _).inv ≫ whiskerRight b.hom G₁₂.mapDerivedCategory ≫
    (associator _ _ _).hom ≫ whiskerLeft F₀₁.mapDerivedCategory c.hom ≫
    (associator _ _ _).inv
  -- Localization detects equality; the common factors below are invertible.
  have ht : τ₁ = τ₂ := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso C₀ (.up ℤ))
    intro X
    dsimp only [τ₁, τ₂, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
      associator_hom_app, associator_inv_app]
    simp only [Category.id_comp, Category.comp_id]
    apply (cancel_mono
      (U₂.mapDerivedCategory.map
        (F₁₂.mapDerivedCategory.map (F₀₁.mapDerivedCategoryFactors.hom.app X)) ≫
       U₂.mapDerivedCategory.map
        (F₁₂.mapDerivedCategoryFactors.hom.app ((F₀₁.mapHomologicalComplex (.up ℤ)).obj X)) ≫
       U₂.mapDerivedCategoryFactors.hom.app
        ((F₁₂.mapHomologicalComplex (.up ℤ)).obj ((F₀₁.mapHomologicalComplex (.up ℤ)).obj X)))).mp
    -- Factor the two composition comparisons through Qh.
    have hdF : dF.hom.app (DerivedCategory.Q.obj X) ≫
        F₁₂.mapDerivedCategory.map (F₀₁.mapDerivedCategoryFactors.hom.app X) ≫
        F₁₂.mapDerivedCategoryFactors.hom.app ((F₀₁.mapHomologicalComplex (.up ℤ)).obj X) =
      F₀₂.mapDerivedCategoryFactors.hom.app X ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex cF.hom (.up ℤ)).app X) := by
      dsimp only [dF, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
      rw [Category.assoc, mapDerivedCategoryCompIso_hom_app_factors,
        mapDerivedCategoryNatIso_fac]
    have hdG : dG.hom.app (DerivedCategory.Q.obj
          ((U₀.mapHomologicalComplex (.up ℤ)).obj X)) ≫
        G₁₂.mapDerivedCategory.map (G₀₁.mapDerivedCategoryFactors.hom.app
          ((U₀.mapHomologicalComplex (.up ℤ)).obj X)) ≫
        G₁₂.mapDerivedCategoryFactors.hom.app
          ((G₀₁.mapHomologicalComplex (.up ℤ)).obj ((U₀.mapHomologicalComplex (.up ℤ)).obj X)) =
      G₀₂.mapDerivedCategoryFactors.hom.app ((U₀.mapHomologicalComplex (.up ℤ)).obj X) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex cG.hom (.up ℤ)).app
          ((U₀.mapHomologicalComplex (.up ℤ)).obj X)) := by
      dsimp only [dG, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
      rw [Category.assoc, mapDerivedCategoryCompIso_hom_app_factors,
        mapDerivedCategoryNatIso_fac]
    -- Normalize the left pasted square using the factorization of q₀₂.
    have hl : a.hom.app (DerivedCategory.Q.obj X) ≫
        U₂.mapDerivedCategory.map (dF.hom.app (DerivedCategory.Q.obj X)) ≫
        U₂.mapDerivedCategory.map
          (F₁₂.mapDerivedCategory.map (F₀₁.mapDerivedCategoryFactors.hom.app X)) ≫
        U₂.mapDerivedCategory.map (F₁₂.mapDerivedCategoryFactors.hom.app
          ((F₀₁.mapHomologicalComplex (.up ℤ)).obj X)) ≫
        U₂.mapDerivedCategoryFactors.hom.app
          ((F₁₂.mapHomologicalComplex (.up ℤ)).obj ((F₀₁.mapHomologicalComplex (.up ℤ)).obj X)) =
      G₀₂.mapDerivedCategory.map (U₀.mapDerivedCategoryFactors.hom.app X) ≫
        G₀₂.mapDerivedCategoryFactors.hom.app ((U₀.mapHomologicalComplex (.up ℤ)).obj X) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex q₀₂.hom (.up ℤ)).app X ≫
            (U₂.mapHomologicalComplex (.up ℤ)).map
              ((NatTrans.mapHomologicalComplex cF.hom (.up ℤ)).app X)) := by
      rw [← U₂.mapDerivedCategory.map_comp_assoc,
        ← U₂.mapDerivedCategory.map_comp_assoc, Category.assoc, hdF,
        U₂.mapDerivedCategory.map_comp_assoc]
      erw [U₂.mapDerivedCategoryFactors.hom.naturality]
      simp only [Functor.comp_map]
      erw [reassoc_of% (exactSquare_fac q₀₂ X)]
      simp only [Functor.map_comp]
    simp only [Category.assoc]
    rw [hl]
    -- Normalize the right pasting, moving factors across the natural comparisons.
    have hn := c.hom.naturality (F₀₁.mapDerivedCategoryFactors.hom.app X)
    dsimp only [Functor.comp_map] at hn
    erw [← reassoc_of% hn]
    erw [exactSquare_fac q₁₂
      ((F₀₁.mapHomologicalComplex (.up ℤ)).obj X)]
    rw [← G₁₂.mapDerivedCategory.map_comp_assoc,
      ← G₁₂.mapDerivedCategory.map_comp_assoc, Category.assoc]
    erw [exactSquare_fac q₀₁ X]
    simp only [Functor.map_comp, Category.assoc]
    erw [reassoc_of% (G₁₂.mapDerivedCategoryFactors.hom.naturality
      ((NatTrans.mapHomologicalComplex q₀₁.hom (.up ℤ)).app X))]
    have hnG := dG.hom.naturality (U₀.mapDerivedCategoryFactors.hom.app X)
    dsimp only [Functor.comp_map] at hnG
    erw [← reassoc_of% hnG, reassoc_of% hdG]
    simpa only [Functor.map_comp, Category.assoc] using congrArg
      (fun f ↦ G₀₂.mapDerivedCategory.map (U₀.mapDerivedCategoryFactors.hom.app X) ≫
        G₀₂.mapDerivedCategoryFactors.hom.app ((U₀.mapHomologicalComplex (.up ℤ)).obj X) ≫
        DerivedCategory.Q.map f) (hqh X)
  simpa only [τ₁, τ₂, a, b, c, dF, dG, NatTrans.comp_app, whiskerLeft_app,
    whiskerRight_app, associator_hom_app, associator_inv_app, Category.id_comp,
    Category.comp_id] using NatTrans.congr_app ht K

private theorem exactSquare_comp_forward
    (q₀₁ : F₀₁ ⋙ U₁ ≅ U₀ ⋙ G₀₁)
    (q₁₂ : F₁₂ ⋙ U₂ ≅ U₁ ⋙ G₁₂)
    (q₀₂ : F₀₂ ⋙ U₂ ≅ U₀ ⋙ G₀₂)
    (cF : F₀₂ ≅ F₀₁ ⋙ F₁₂) (cG : G₀₂ ≅ G₀₁ ⋙ G₁₂)
    (hq : ∀ X : C₀,
      U₂.map (cF.hom.app X) ≫ q₁₂.hom.app (F₀₁.obj X) ≫
        G₁₂.map (q₀₁.hom.app X) = q₀₂.hom.app X ≫ cG.hom.app (U₀.obj X))
    (K : DerivedCategory C₀) :
    U₂.mapDerivedCategory.map
        ((mapDerivedCategoryNatIso cF ≪≫
          (mapDerivedCategoryCompIso F₀₁ F₁₂).symm).hom.app K) ≫
      (mapDerivedCategorySquareIso q₁₂).hom.app (F₀₁.mapDerivedCategory.obj K) ≫
      G₁₂.mapDerivedCategory.map ((mapDerivedCategorySquareIso q₀₁).hom.app K) =
    (mapDerivedCategorySquareIso q₀₂).hom.app K ≫
      (mapDerivedCategoryNatIso cG ≪≫ (mapDerivedCategoryCompIso G₀₁ G₁₂).symm).hom.app
        (U₀.mapDerivedCategory.obj K) := by
  have hi (X : C₀) := square_reverse G₁₂ (q₀₂.app X)
    (q₁₂.app (F₀₁.obj X)) (q₀₁.app X)
    (U₂.map (cF.hom.app X)) (cG.hom.app (U₀.obj X)) (hq X)
  have hd := exactSquare_comp_inverse F₀₁ F₁₂ F₀₂ G₀₁ G₁₂ G₀₂ U₀ U₁ U₂
    q₀₁.symm q₁₂.symm q₀₂.symm cF cG hi K
  simp only [square_symm_hom] at hd
  exact square_forward G₁₂.mapDerivedCategory
    ((mapDerivedCategorySquareIso q₀₂).app K)
    ((mapDerivedCategorySquareIso q₁₂).app (F₀₁.mapDerivedCategory.obj K))
    ((mapDerivedCategorySquareIso q₀₁).app K) _ _ hd

/-- Exact derived square comparisons respect a specified composition identity as natural
isomorphisms, before taking components.
Source: the localization universal property, Stacks Project, Tags 05S7 and 014F.
(auxiliary; not a blueprint node).

Proof: First invert the ordinary comparison square by cancelling its three isomorphisms.
Apply its resulting component equation degreewise to cochain complexes. Form the two
natural transformations after localization and use localization extensionality for Q.
Postcompose both sides with the three invertible localization factors for F₀₁, F₁₂ and U₂.
Naturality and the square/compositor factorization identities reduce both sides to Q
applied to the given degreewise equation, preceded by the same factors. Cancel the
factors and use localization extensionality. Invert the derived square by the same
cancellation, and apply natural-transformation extensionality to obtain the displayed
identity of natural isomorphisms. Keeping this equality before taking components avoids
unfolding concrete localization morphisms when specializing to chosen category models.
No boundedness, nonzero-object, resolution, or preservation-of-injectives hypothesis is used. -/
theorem mapDerivedCategorySquareIso_comp
    (q₀₁ : F₀₁ ⋙ U₁ ≅ U₀ ⋙ G₀₁)
    (q₁₂ : F₁₂ ⋙ U₂ ≅ U₁ ⋙ G₁₂)
    (q₀₂ : F₀₂ ⋙ U₂ ≅ U₀ ⋙ G₀₂)
    (cF : F₀₂ ≅ F₀₁ ⋙ F₁₂) (cG : G₀₂ ≅ G₀₁ ⋙ G₁₂)
    (hq : ∀ X : C₀,
      U₂.map (cF.hom.app X) ≫ q₁₂.hom.app (F₀₁.obj X) ≫
        G₁₂.map (q₀₁.hom.app X) = q₀₂.hom.app X ≫ cG.hom.app (U₀.obj X)) :
    isoWhiskerRight
        (mapDerivedCategoryNatIso cF ≪≫ (mapDerivedCategoryCompIso F₀₁ F₁₂).symm)
        U₂.mapDerivedCategory ≪≫
      (associator F₀₁.mapDerivedCategory F₁₂.mapDerivedCategory U₂.mapDerivedCategory ≪≫
        isoWhiskerLeft F₀₁.mapDerivedCategory (mapDerivedCategorySquareIso q₁₂) ≪≫
        (associator F₀₁.mapDerivedCategory U₁.mapDerivedCategory G₁₂.mapDerivedCategory).symm ≪≫
        isoWhiskerRight (mapDerivedCategorySquareIso q₀₁) G₁₂.mapDerivedCategory ≪≫
        associator U₀.mapDerivedCategory G₀₁.mapDerivedCategory G₁₂.mapDerivedCategory) =
    mapDerivedCategorySquareIso q₀₂ ≪≫ isoWhiskerLeft U₀.mapDerivedCategory
      (mapDerivedCategoryNatIso cG ≪≫ (mapDerivedCategoryCompIso G₀₁ G₁₂).symm) := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app, associator_hom_app,
    associator_inv_app, Category.id_comp, Category.comp_id] using
    exactSquare_comp_forward F₀₁ F₁₂ F₀₂ G₀₁ G₁₂ G₀₂ U₀ U₁ U₂
      q₀₁ q₁₂ q₀₂ cF cG hq K

end Composition

end CategoryTheory.Functor
