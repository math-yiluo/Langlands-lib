/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange

/-! # Lifting a commuting cube to bounded below right derived functors

Source: Stacks Project, Tag 0736, uniqueness of right derived transformations.
(blueprint: lem-weil-pbc-right-derived-plus-cube)
-/

@[expose] public section

open CategoryTheory Limits
open scoped CategoryTheory.Functor

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

namespace CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- The derived lift of an exact comparison agrees with its termwise map after localization. -/
private lemma exactComparison_factorsh
    {X Y Y' Z : Type*} [Category* X] [Category* Y] [Category* Y'] [Category* Z]
    [Abelian X] [Abelian Y] [Abelian Y'] [Abelian Z]
    [HasDerivedCategory X] [HasDerivedCategory Y]
    [HasDerivedCategory Y'] [HasDerivedCategory Z]
    (F : X ⥤ Y) (J : Y ⥤ Z) (F' : X ⥤ Y') (J' : Y' ⥤ Z)
    [F.Additive] [J.Additive] [F'.Additive] [J'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    [PreservesFiniteLimits J'] [PreservesFiniteColimits J']
    (t : F ⋙ J ≅ F' ⋙ J') (M : HomotopyCategory.Plus X) :
    ((mapDerivedCategoryPlusCompIso F J).symm ≪≫ mapDerivedCategoryPlusNatIso t ≪≫
        mapDerivedCategoryPlusCompIso F' J').hom.app (DerivedCategory.Plus.Qh.obj M) ≫
      D+(J').map (F'.mapDerivedCategoryPlusFactorsh.hom.app M) ≫
      J'.mapDerivedCategoryPlusFactorsh.hom.app (F'.mapHomotopyCategoryPlus.obj M) =
    D+(J).map (F.mapDerivedCategoryPlusFactorsh.hom.app M) ≫
      J.mapDerivedCategoryPlusFactorsh.hom.app (F.mapHomotopyCategoryPlus.obj M) ≫
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus t.hom).app M) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [mapDerivedCategoryPlusCompIso_hom_app_factorsh F' J' M]
  rw [mapDerivedCategoryPlusNatIso_hom_app_factorsh t M]
  have hf := mapDerivedCategoryPlusCompIso_hom_app_factorsh F J M
  rw [← hf]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

/-- Inverting the preceding factorization gives the compatibility for inverse comparisons. -/
private lemma exactComparison_inv_factorsh
    {X Y Y' Z : Type*} [Category* X] [Category* Y] [Category* Y'] [Category* Z]
    [Abelian X] [Abelian Y] [Abelian Y'] [Abelian Z]
    [HasDerivedCategory X] [HasDerivedCategory Y]
    [HasDerivedCategory Y'] [HasDerivedCategory Z]
    (F : X ⥤ Y) (J : Y ⥤ Z) (F' : X ⥤ Y') (J' : Y' ⥤ Z)
    [F.Additive] [J.Additive] [F'.Additive] [J'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    [PreservesFiniteLimits J'] [PreservesFiniteColimits J']
    (t : F ⋙ J ≅ F' ⋙ J') (M : HomotopyCategory.Plus X) :
    J'.mapDerivedCategoryPlusFactorsh.inv.app (F'.mapHomotopyCategoryPlus.obj M) ≫
      D+(J').map (F'.mapDerivedCategoryPlusFactorsh.inv.app M) ≫
      ((mapDerivedCategoryPlusCompIso F J).symm ≪≫ mapDerivedCategoryPlusNatIso t ≪≫
        mapDerivedCategoryPlusCompIso F' J').inv.app (DerivedCategory.Plus.Qh.obj M) =
    DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus t.inv).app M) ≫
      J.mapDerivedCategoryPlusFactorsh.inv.app (F.mapHomotopyCategoryPlus.obj M) ≫
      D+(J).map (F.mapDerivedCategoryPlusFactorsh.inv.app M) := by
  let A := D+(J).mapIso (F.mapDerivedCategoryPlusFactorsh.app M) ≪≫
    J.mapDerivedCategoryPlusFactorsh.app (F.mapHomotopyCategoryPlus.obj M)
  let A' := D+(J').mapIso (F'.mapDerivedCategoryPlusFactorsh.app M) ≪≫
    J'.mapDerivedCategoryPlusFactorsh.app (F'.mapHomotopyCategoryPlus.obj M)
  let r : (F ⋙ J).mapHomotopyCategoryPlus ≅ (F' ⋙ J').mapHomotopyCategoryPlus :=
    { hom := NatTrans.mapHomotopyCategoryPlus t.hom
      inv := NatTrans.mapHomotopyCategoryPlus t.inv
      hom_inv_id := by
        rw [← NatTrans.mapHomotopyCategoryPlus_comp, Iso.hom_inv_id,
          NatTrans.mapHomotopyCategoryPlus_id]
      inv_hom_id := by
        rw [← NatTrans.mapHomotopyCategoryPlus_comp, Iso.inv_hom_id,
          NatTrans.mapHomotopyCategoryPlus_id] }
  have hi : (((mapDerivedCategoryPlusCompIso F J).symm ≪≫
      mapDerivedCategoryPlusNatIso t ≪≫ mapDerivedCategoryPlusCompIso F' J').app
        (DerivedCategory.Plus.Qh.obj M)) ≪≫ A' =
      A ≪≫ DerivedCategory.Plus.Qh.mapIso (r.app M) := by
    apply Iso.ext
    simpa only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
      A, A', r, Category.assoc] using exactComparison_factorsh F J F' J' t M
  simpa only [Iso.trans_inv, Iso.app_inv, Functor.mapIso_inv,
    A, A', r, Category.assoc] using congrArg Iso.inv hi

variable {B C B' C' B₀ C₀ B₀' C₀' : Type*}
  [Category* B] [Category* C] [Category* B'] [Category* C']
  [Category* B₀] [Category* C₀] [Category* B₀'] [Category* C₀']
  [Abelian B] [Abelian C] [Abelian B'] [Abelian C']
  [Abelian B₀] [Abelian C₀] [Abelian B₀'] [Abelian C₀']
  [HasDerivedCategory B] [HasDerivedCategory C]
  [HasDerivedCategory B'] [HasDerivedCategory C']
  [HasDerivedCategory B₀] [HasDerivedCategory C₀]
  [HasDerivedCategory B₀'] [HasDerivedCategory C₀']
  [EnoughInjectives B] [EnoughInjectives B']
  [EnoughInjectives B₀] [EnoughInjectives B₀']
  (G : B ⥤ C) (H : B' ⥤ C') (G₀ : B₀ ⥤ C₀) (H₀ : B₀' ⥤ C₀')
  (P : B ⥤ B') (Q : C ⥤ C') (P₀ : B₀ ⥤ B₀') (Q₀ : C₀ ⥤ C₀')
  (U : B ⥤ B₀) (V : C ⥤ C₀) (U' : B' ⥤ B₀') (V' : C' ⥤ C₀')
  [G.Additive] [H.Additive] [G₀.Additive] [H₀.Additive]
  [P.Additive] [Q.Additive] [P₀.Additive] [Q₀.Additive]
  [U.Additive] [V.Additive] [U'.Additive] [V'.Additive]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
  [PreservesFiniteLimits P₀] [PreservesFiniteColimits P₀]
  [PreservesFiniteLimits Q₀] [PreservesFiniteColimits Q₀]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  [PreservesFiniteLimits V] [PreservesFiniteColimits V]
  [PreservesFiniteLimits U'] [PreservesFiniteColimits U']
  [PreservesFiniteLimits V'] [PreservesFiniteColimits V']

/-- A commuting cube with exact transverse edges remains commuting after right derivation.

Source: Stacks Project, Tag 0736, construction and uniqueness of derived transformations.
(blueprint: lem-weil-pbc-right-derived-plus-cube)

Proof: Compare the two natural transformations from RG followed by DQ and DV'.
Precompose with the unit of RG, whiskered by DQ and DV'. The factorization
identity for each rightDerivedFunctorPlusBaseChange replaces its derived
comparison by the corresponding termwise map followed by the target derived
unit. The factorization identities for mapDerivedCategoryPlusCompIso and
mapDerivedCategoryPlusNatIso replace the two exact comparison isomorphisms
by their maps on homotopy categories. Naturality of the unit of RH₀ moves
these comparison maps past the final unit. The two resulting composites are
the images of the assumed underived cube equation, followed by the same
unit of RH₀. They are equal. The composite RG ⋙ DQ ⋙ DV' is an absolute
right derived functor, so rightDerived_ext proves equality of the natural
transformations. Evaluate at K. This uses no preservation of injectives by
U or U', and does not require invertibility of a or b. -/
theorem rightDerivedFunctorPlusBaseChange_cube
    (e : G ⋙ Q ⟶ P ⋙ H) (e₀ : G₀ ⋙ Q₀ ⟶ P₀ ⋙ H₀)
    (a : G ⋙ V ⟶ U ⋙ G₀) (b : H ⋙ V' ⟶ U' ⋙ H₀)
    (c : V ⋙ Q₀ ≅ Q ⋙ V') (d : U ⋙ P₀ ≅ P ⋙ U')
    (h : ∀ F : B, V'.map (e.app F) ≫ b.app (P.obj F) ≫ H₀.map (d.inv.app F) =
      c.inv.app (G.obj F) ≫ Q₀.map (a.app F) ≫ e₀.app (U.obj F))
    (K : DerivedCategory.Plus B) :
    D+(V').map ((rightDerivedFunctorPlusBaseChange e).app K) ≫
        (rightDerivedFunctorPlusBaseChange b).app (D+(P).obj K) ≫
        R+(H₀).map (((mapDerivedCategoryPlusCompIso U P₀).symm ≪≫
          mapDerivedCategoryPlusNatIso d ≪≫ mapDerivedCategoryPlusCompIso P U').inv.app K) =
      ((mapDerivedCategoryPlusCompIso V Q₀).symm ≪≫
        mapDerivedCategoryPlusNatIso c ≪≫ mapDerivedCategoryPlusCompIso Q V').inv.app
          (R+(G).obj K) ≫
        D+(Q₀).map ((rightDerivedFunctorPlusBaseChange a).app K) ≫
        (rightDerivedFunctorPlusBaseChange e₀).app (D+(U).obj K) := by
  let dc := (mapDerivedCategoryPlusCompIso V Q₀).symm ≪≫
    mapDerivedCategoryPlusNatIso c ≪≫ mapDerivedCategoryPlusCompIso Q V'
  let dd := (mapDerivedCategoryPlusCompIso U P₀).symm ≪≫
    mapDerivedCategoryPlusNatIso d ≪≫ mapDerivedCategoryPlusCompIso P U'
  let α : R+(G) ⋙ (D+(Q) ⋙ D+(V')) ⟶ (D+(U) ⋙ D+(P₀)) ⋙ R+(H₀) :=
    Functor.whiskerRight (rightDerivedFunctorPlusBaseChange e) D+(V') ≫
    Functor.whiskerLeft D+(P) (rightDerivedFunctorPlusBaseChange b) ≫
    Functor.whiskerRight dd.inv R+(H₀)
  let β : R+(G) ⋙ (D+(Q) ⋙ D+(V')) ⟶ (D+(U) ⋙ D+(P₀)) ⋙ R+(H₀) :=
    Functor.whiskerLeft R+(G) dc.inv ≫
    Functor.whiskerRight (rightDerivedFunctorPlusBaseChange a) D+(Q₀) ≫
    Functor.whiskerLeft D+(U) (rightDerivedFunctorPlusBaseChange e₀)
  -- Absoluteness reduces equality to compatibility on the homotopy category.
  have heq : α = β := by
    apply Functor.rightDerived_ext (R+(G) ⋙ (D+(Q) ⋙ D+(V')))
      (Functor.whiskerRight G.rightDerivedFunctorPlusUnith (D+(Q) ⋙ D+(V')) ≫
        (Functor.associator _ _ _).hom) (HomotopyCategory.Plus.quasiIso B)
    apply NatTrans.ext
    funext M
    simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
      Functor.associator_hom_app, Category.id_comp,
      Functor.comp_map, α, β, Category.assoc]
    -- Replace the first two derived faces by their defining unit factorizations.
    have he := congr_app (rightDerivedFunctorPlusBaseChange_fac e) M
    have ha := congr_app (rightDerivedFunctorPlusBaseChange_fac a) M
    simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
      Functor.associator_hom_app, Category.comp_id, Functor.comp_obj] at he ha
    rw [← D+(V').map_comp_assoc, he]
    have hc := dc.inv.naturality (G.rightDerivedFunctorPlusUnith.app M)
    simp only [Functor.comp_map] at hc
    rw [reassoc_of% hc, ← D+(Q₀).map_comp_assoc, ha]
    simp only [rightDerivedFunctorPlusBaseChangeAux, NatTrans.comp_app,
      whiskerRight_app, whiskerLeft_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp, Category.comp_id,
      Functor.map_comp, Category.assoc]
    -- Move the localization comparisons through the remaining faces and factor them.
    have hb := (rightDerivedFunctorPlusBaseChange b).naturality
      (P.mapDerivedCategoryPlusFactorsh.inv.app M)
    have he₀ := (rightDerivedFunctorPlusBaseChange e₀).naturality
      (U.mapDerivedCategoryPlusFactorsh.inv.app M)
    simp only [Functor.comp_map, Functor.comp_obj] at hb he₀
    rw [reassoc_of% hb, he₀]
    have hbf := congr_app (rightDerivedFunctorPlusBaseChange_fac b)
      (P.mapHomotopyCategoryPlus.obj M)
    have he₀f := congr_app (rightDerivedFunctorPlusBaseChange_fac e₀)
      (U.mapHomotopyCategoryPlus.obj M)
    simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
      Functor.associator_hom_app, Category.comp_id, Functor.comp_obj] at hbf he₀f
    rw [reassoc_of% hbf, reassoc_of% he₀f]
    simp only [rightDerivedFunctorPlusBaseChangeAux, NatTrans.comp_app,
      whiskerRight_app, whiskerLeft_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp, Category.comp_id,
      Category.assoc]
    simp only [mapHomotopyCategoryPlusCompIso_refl_hom_app,
      mapHomotopyCategoryPlusCompIso_refl_inv_app]
    simp only [Functor.map_id, Category.id_comp, Functor.comp_obj]
    have hv := V'.mapDerivedCategoryPlusFactorsh.hom.naturality
      ((NatTrans.mapHomotopyCategoryPlus e).app M)
    have hq := Q₀.mapDerivedCategoryPlusFactorsh.hom.naturality
      ((NatTrans.mapHomotopyCategoryPlus a).app M)
    simp only [Functor.comp_map, Functor.comp_obj] at hv hq
    erw [reassoc_of% hv, reassoc_of% hq]
    -- Express the two exact edges by their termwise comparisons.
    have hd := exactComparison_inv_factorsh U P₀ P U' d M
    change U'.mapDerivedCategoryPlusFactorsh.inv.app (P.mapHomotopyCategoryPlus.obj M) ≫
      D+(U').map (P.mapDerivedCategoryPlusFactorsh.inv.app M) ≫
      dd.inv.app (DerivedCategory.Plus.Qh.obj M) = _ at hd
    rw [← R+(H₀).map_comp, ← R+(H₀).map_comp, hd]
    simp only [Functor.map_comp]
    have hn := H₀.rightDerivedFunctorPlusUnith.naturality
      ((NatTrans.mapHomotopyCategoryPlus d.inv).app M)
    simp only [Functor.comp_map] at hn
    erw [← reassoc_of% hn]
    have hcf := exactComparison_factorsh V Q₀ Q V' c (G.mapHomotopyCategoryPlus.obj M)
    have hci : dc.inv.app (DerivedCategory.Plus.Qh.obj (G.mapHomotopyCategoryPlus.obj M)) ≫
        D+(Q₀).map (V.mapDerivedCategoryPlusFactorsh.hom.app
          (G.mapHomotopyCategoryPlus.obj M)) ≫
        Q₀.mapDerivedCategoryPlusFactorsh.hom.app
          (V.mapHomotopyCategoryPlus.obj (G.mapHomotopyCategoryPlus.obj M)) =
      D+(V').map (Q.mapDerivedCategoryPlusFactorsh.hom.app
          (G.mapHomotopyCategoryPlus.obj M)) ≫
        V'.mapDerivedCategoryPlusFactorsh.hom.app
          (Q.mapHomotopyCategoryPlus.obj (G.mapHomotopyCategoryPlus.obj M)) ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus c.inv).app
          (G.mapHomotopyCategoryPlus.obj M)) := by
      apply (cancel_epi (dc.hom.app
        (DerivedCategory.Plus.Qh.obj (G.mapHomotopyCategoryPlus.obj M)))).1
      simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
      erw [Category.assoc, Category.assoc, reassoc_of% hcf]
      simp only [← DerivedCategory.Plus.Qh.map_comp,
        ← NatTrans.comp_app, ← NatTrans.mapHomotopyCategoryPlus_comp,
        Iso.hom_inv_id, NatTrans.mapHomotopyCategoryPlus_id, NatTrans.id_app]
      erw [Functor.map_id, Category.comp_id]
    erw [reassoc_of% hci]
    -- The resulting termwise composites are equal by the underived cube hypothesis.
    let l : G ⋙ Q ⋙ V' ⟶ (U ⋙ P₀) ⋙ H₀ :=
      Functor.whiskerRight e V' ≫ Functor.whiskerLeft P b ≫ Functor.whiskerRight d.inv H₀
    let r : G ⋙ Q ⋙ V' ⟶ (U ⋙ P₀) ⋙ H₀ :=
      Functor.whiskerLeft G c.inv ≫ Functor.whiskerRight a Q₀ ≫ Functor.whiskerLeft U e₀
    have hlr : l = r := by
      apply NatTrans.ext
      funext F
      exact h F
    have hh : V'.mapHomotopyCategoryPlus.map ((NatTrans.mapHomotopyCategoryPlus e).app M) ≫
          (NatTrans.mapHomotopyCategoryPlus b).app (P.mapHomotopyCategoryPlus.obj M) ≫
          H₀.mapHomotopyCategoryPlus.map ((NatTrans.mapHomotopyCategoryPlus d.inv).app M) =
        (NatTrans.mapHomotopyCategoryPlus c.inv).app (G.mapHomotopyCategoryPlus.obj M) ≫
          Q₀.mapHomotopyCategoryPlus.map ((NatTrans.mapHomotopyCategoryPlus a).app M) ≫
          (NatTrans.mapHomotopyCategoryPlus e₀).app (U.mapHomotopyCategoryPlus.obj M) := by
      have ht := congr_app (congrArg NatTrans.mapHomotopyCategoryPlus hlr) M
      simp only [l, r, NatTrans.mapHomotopyCategoryPlus_comp, NatTrans.comp_app] at ht
      exact ht
    have hqh := congrArg DerivedCategory.Plus.Qh.map hh
    simp only [Functor.map_comp] at hqh
    erw [reassoc_of% hqh]
    rfl
  simpa [α, β, dc, dd] using congr_app heq K

end CategoryTheory.Functor
