/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence

/-! # Composition of the tensor comparison for extension by zero

Source: Stacks Project, Tags 0GL1 and 0E8I.
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false

universe u u'

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

private theorem inverse_congr
    {C : Type*} [Category C] {X Y : C} {f g : X ⟶ Y} [IsIso f] [IsIso g]
    (h : f = g) : inv f = inv g := by
  subst g
  rfl

private theorem inv_bifunctor_component
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F G : C ⥤ D ⥤ E} (e : F ≅ G) (M : C) (N : D) :
    inv ((e.hom.app M).app N) = (e.inv.app M).app N :=
  NatIso.inv_hom_app (e.app M) N

private theorem left_projection_comp
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F : C ⥤ D} {R : D ⥤ C} {G : D ⥤ E} {S : E ⥤ D}
    (adj : F ⊣ R) (adj' : G ⊣ S) (Lf : D ⥤ C) (Lg : E ⥤ D)
    (T : C ⥤ C ⥤ C) (U : D ⥤ D ⥤ D) (V : E ⥤ E ⥤ E)
    (δf : (((Functor.whiskeringLeft₂ C).obj R).obj Lf).obj T ⟶
      (Functor.postcompose₂.obj R).obj U)
    (δg : (((Functor.whiskeringLeft₂ D).obj S).obj Lg).obj U ⟶
      (Functor.postcompose₂.obj S).obj V)
    (M : C) (N : E) :
    let δc : (((Functor.whiskeringLeft₂ C).obj (S ⋙ R)).obj (Lg ⋙ Lf)).obj T ⟶
        (Functor.postcompose₂.obj (S ⋙ R)).obj V :=
      (((Functor.whiskeringLeft₂ C).obj S).obj Lg).map δf ≫
        (Functor.postcompose₂.obj R).map δg
    (((adj.comp adj').projectionMap (Lg ⋙ Lf) T V δc).app M).app N =
      G.map (((adj.projectionMap Lf T U δf).app M).app (Lg.obj N)) ≫
        ((adj'.projectionMap Lg U V δg).app (F.obj M)).app N := by
  intro δc
  let pf := ((adj.projectionMap Lf T U δf).app M).app (Lg.obj N)
  let pg := ((adj'.projectionMap Lg U V δg).app (F.obj M)).app N
  apply ((adj.comp adj').homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.unit_app_comp_map_projectionMap_app_app]
  rw [Adjunction.homEquiv_unit, Adjunction.comp_unit_app]
  dsimp only [Functor.comp_map]
  simp only [Functor.map_comp, Category.assoc]
  have hu := adj'.unit.naturality pf
  dsimp only [Functor.comp_map, Functor.id_map] at hu
  have hur := congrArg R.map hu
  simp only [Functor.map_comp] at hur
  erw [← reassoc_of% hur]
  have hg := adj'.unit_app_comp_map_projectionMap_app_app Lg U V δg (F.obj M) N
  have hgr := congrArg R.map hg
  simp only [Functor.map_comp] at hgr
  erw [hgr]
  have hf := adj.unit_app_comp_map_projectionMap_app_app Lf T U δf M (Lg.obj N)
  erw [reassoc_of% hf]
  simp only [Adjunction.projectionMapTranspose_app_app, Functor.map_comp, Category.assoc]
  have hn := congr_app (δf.naturality (adj'.unit.app (F.obj M))) (Lg.obj N)
  dsimp only [Functor.postcompose₂, Functor.whiskeringLeft₂, Functor.whiskeringRight,
    Functor.whiskeringLeft, Functor.comp_map, Functor.comp_obj, NatTrans.comp_app] at hn
  erw [← reassoc_of% hn]
  simp only [ Adjunction.comp_unit_app,
    δc, Functor.map_comp, NatTrans.comp_app, Category.assoc]
  rfl

private theorem left_tensor_comparison_comp
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F R : D ⥤ C) (G S : E ⥤ D)
    (T : C ⥤ C ⥤ C) (U : D ⥤ D ⥤ D) (V : E ⥤ E ⥤ E)
    (lf : F ≅ R) (lg : G ≅ S)
    (cf : (Functor.postcompose₂.obj F).obj U ≅
      (((Functor.whiskeringLeft₂ C).obj F).obj F).obj T)
    (cg : (Functor.postcompose₂.obj G).obj V ≅
      (((Functor.whiskeringLeft₂ D).obj G).obj G).obj U)
    (M N : E) :
    let l := Functor.isoWhiskerRight lg F ≪≫ Functor.isoWhiskerLeft S lf
    (T.map (lf.inv.app (S.obj M))).app (F.obj (G.obj N)) ≫
        (cf.inv.app (S.obj M)).app (G.obj N) ≫
        lf.hom.app ((U.obj (S.obj M)).obj (G.obj N)) ≫
        R.map ((U.map (lg.inv.app M)).app (G.obj N) ≫
          (cg.inv.app M).app N ≫ lg.hom.app ((V.obj M).obj N)) =
      (T.map (l.inv.app M)).app (F.obj (G.obj N)) ≫
        (cf.inv.app (G.obj M)).app (G.obj N) ≫
        F.map ((cg.inv.app M).app N) ≫ l.hom.app ((V.obj M).obj N) := by
  intro l
  have hn := lf.hom.naturality ((U.map (lg.inv.app M)).app (G.obj N) ≫
    (cg.inv.app M).app N ≫ lg.hom.app ((V.obj M).obj N))
  rw [← hn]
  simp only [Functor.map_comp, Category.assoc]
  have hc := congr_app (cf.inv.naturality (lg.inv.app M)) (G.obj N)
  dsimp only [Functor.postcompose₂, Functor.whiskeringLeft₂,
    Functor.whiskeringLeft, Functor.whiskeringRight, Functor.comp_obj,
    Functor.comp_map, NatTrans.comp_app] at hc
  erw [← reassoc_of% hc]
  simp only [l, Iso.trans_hom, Iso.trans_inv, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, NatTrans.comp_app, Functor.map_comp, Category.assoc]

private theorem iso_square_inverse
    {C : Type*} [Category C] {W X Y Z : C}
    (a : W ≅ X) (b : Y ≅ Z) (p : W ⟶ Y) (q : X ⟶ Z)
    (h : p ≫ b.hom = a.hom ≫ q) : q ≫ b.inv = a.inv ≫ p := by
  apply (cancel_mono b.hom).1
  simp only [Category.assoc, b.inv_hom_id, Category.comp_id, h, a.inv_hom_id_assoc]

private theorem left_tensor_comparison_transport
    {C D : Type*} [Category C] [Category D]
    (F F' R R' : D ⥤ C) (T : C ⥤ C ⥤ C) (U : D ⥤ D ⥤ D)
    (a : F' ≅ F) (b : R' ≅ R) (l : F ≅ R) (l' : F' ≅ R')
    (cf : (Functor.postcompose₂.obj F).obj U ≅
      (((Functor.whiskeringLeft₂ C).obj F).obj F).obj T)
    (cf' : (Functor.postcompose₂.obj F').obj U ≅
      (((Functor.whiskeringLeft₂ C).obj F').obj F').obj T)
    (hl : ∀ X, a.hom.app X ≫ l.hom.app X = l'.hom.app X ≫ b.hom.app X)
    (hc : ∀ M N,
      a.hom.app ((U.obj M).obj N) ≫ (cf.hom.app M).app N =
        (cf'.hom.app M).app N ≫
          (T.map (a.hom.app M)).app (F'.obj N) ≫
          (T.obj (F.obj M)).map (a.hom.app N))
    (M N : D) :
    (T.map (l.inv.app M)).app (F.obj N) ≫ (cf.inv.app M).app N ≫
        l.hom.app ((U.obj M).obj N) ≫ b.inv.app ((U.obj M).obj N) =
      (T.map (b.inv.app M)).app (F.obj N) ≫
        (T.obj (R'.obj M)).map (a.inv.app N) ≫
        (T.map (l'.inv.app M)).app (F'.obj N) ≫
        (cf'.inv.app M).app N ≫ l'.hom.app ((U.obj M).obj N) := by
  let tt := ((T.mapIso (a.app M)).app (F'.obj N)) ≪≫
    (T.obj (F.obj M)).mapIso (a.app N)
  have hc' : (cf'.hom.app M).app N ≫ tt.hom =
      a.hom.app ((U.obj M).obj N) ≫ (cf.hom.app M).app N := by
    simpa only [tt, Iso.trans_hom, Functor.mapIso_hom,
      Iso.app_hom, Category.assoc] using (hc M N).symm
  have hc0 := iso_square_inverse ((cf'.app M).app N) ((cf.app M).app N)
    (a.hom.app ((U.obj M).obj N)) tt.hom hc'.symm
  have hci := iso_square_inverse tt (a.app ((U.obj M).obj N))
    ((cf'.inv.app M).app N) ((cf.inv.app M).app N) hc0.symm
  have hli := iso_square_inverse (a.app ((U.obj M).obj N))
    (b.app ((U.obj M).obj N)) (l'.hom.app _) (l.hom.app _) (hl _).symm
  have hinv : l.inv.app M ≫ a.inv.app M = b.inv.app M ≫ l'.inv.app M := by
    apply (cancel_mono (a.hom.app M ≫ l.hom.app M)).1
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
    rw [hl M]
    simp only [Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  simp only [Iso.app_inv] at hci hli
  rw [hli]
  rw [reassoc_of% hci]
  simp only [tt, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv,
    Category.assoc]
  have hn := (T.map (a.inv.app M)).naturality (a.inv.app N)
  rw [reassoc_of% hn]
  have hn' := (T.map (l'.inv.app M)).naturality (a.inv.app N)
  rw [reassoc_of% hn']
  simp only [← NatTrans.comp_app_assoc, ← T.map_comp, hinv]

namespace AlgebraicGeometry.Etale

variable (B : Type u') [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [HasSmallSiteSheafify B]
  [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B]
  [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
  [UpperStarPreservesFlat B]
  {FC : B → B → Type*} {CC : B → Type (u + 1)}
  [∀ (P Q : B), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} B FC]
  [(CategoryTheory.forget B).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget B)]
  [∀ (Z : Scheme.{u}), Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget B)]

omit [HasSmallSiteSheafify B] [UpperStarPreservesFlat B] in
private theorem derived_open_unit
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    (derivedOpenImmersionLowerShriekUpperStarAdjunction B j).unit =
      ((Functor.mapDerivedCategoryIdIso (Sheaf X.smallEtaleTopology B)).symm ≪≫
        Functor.mapDerivedCategoryNatIso
          (asIso (openImmersionLowerShriekUpperStarAdjunction B j).unit) ≪≫
        (Functor.mapDerivedCategoryCompIso (openImmersionLowerShriek B j)
          (upperStar B j)).symm).hom := by
  rw [derivedOpenImmersionLowerShriekUpperStarAdjunction]
  let J := openImmersionLowerShriek B j
  let R := upperStar B j
  let adj := openImmersionLowerShriekUpperStarAdjunction B j
  refine Localization.natTrans_ext DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Sheaf X.smallEtaleTopology B) (.up ℤ)) (fun K ↦ ?_)
  rw [← cancel_mono (R.mapDerivedCategory.map (J.mapDerivedCategoryFactorsh.hom.app K) ≫
    R.mapDerivedCategoryFactorsh.hom.app ((J.mapHomotopyCategory (.up ℤ)).obj K))]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [Adjunction.mapDerivedCategoryAdjunction_unit_app_Qh_obj,
    Functor.mapDerivedCategoryCompIso_hom_app_factorsh,
    Functor.mapDerivedCategoryNatIso_fach,
    ← Functor.mapDerivedCategoryIdIso_hom_app_Qh_obj]
  simp only [Iso.inv_hom_id_app_assoc]
  congr 1
  obtain ⟨C, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  rw [Adjunction.mapHomotopyCategory_unit_app_quotient]
  rfl

private noncomputable def openCompanionTriangle
    {X Y Z : Scheme.{u}} (j : X ⟶ Y) (b : Y ⟶ Z)
    [IsOpenImmersion j] [IsOpenImmersion b] :
    upperStar B j ≅ openImmersionLowerShriek B b ⋙ upperStar B (j ≫ b) :=
  (upperStar B j).leftUnitor.symm ≪≫
    Functor.isoWhiskerRight
      (asIso (openImmersionLowerShriekUpperStarAdjunction B b).unit) (upperStar B j) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (openImmersionLowerShriek B b) (upperStarComp B j b).symm

omit [HasSmallSiteSheafify B] [MonoidalCategory B] [MonoidalPreadditive B]
  [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
  [UpperStarPreservesFlat B] in
private theorem open_companion_unit
    {X Y Z : Scheme.{u}} (j : X ⟶ Y) (b : Y ⟶ Z)
    [IsOpenImmersion j] [IsOpenImmersion b]
    (M : Sheaf X.smallEtaleTopology B) :
    (openImmersionLowerShriekUpperStarAdjunction B (j ≫ b)).unit.app M ≫
        (upperStar B (j ≫ b)).map ((openImmersionLowerShriekComp B j b).hom.app M) =
      (openImmersionLowerShriekUpperStarAdjunction B j).unit.app M ≫
        (openCompanionTriangle B j b).hom.app ((openImmersionLowerShriek B j).obj M) := by
  rw [openImmersionLowerShriekComp, Adjunction.unit_leftAdjointUniq_hom_app]
  simp only [Adjunction.ofNatIsoRight_unit, Adjunction.comp_unit_app,
    NatTrans.comp_app, Functor.whiskerLeft_app, Iso.symm_hom,
    openCompanionTriangle, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom,
    Functor.leftUnitor_inv_app, Functor.associator_hom_app, asIso_hom,
    Category.id_comp, Category.assoc, Functor.comp_obj]

section

attribute [local irreducible] Functor.mapDerivedCategory

omit [HasSmallSiteSheafify B] [UpperStarPreservesFlat B] in
private theorem derived_open_companion
    {X Y Z : Scheme.{u}} (j : X ⟶ Y) (b : Y ⟶ Z)
    [IsOpenImmersion j] [IsOpenImmersion b]
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology B)) :
    (Functor.mapDerivedCategoryTriangleIso (openCompanionTriangle B j b)).hom.app K =
      (upperStar B j).mapDerivedCategory.map
          ((derivedOpenImmersionLowerShriekUpperStarAdjunction B b).unit.app K) ≫
        (Functor.mapDerivedCategoryTriangleIso (upperStarComp B j b)).inv.app
          ((openImmersionLowerShriek B b).mapDerivedCategory.obj K) := by
  let J := openImmersionLowerShriek B b
  let R := upperStar B b
  let S := upperStar B j
  let t := upperStarComp B j b
  let U := (upperStar B (j ≫ b)).mapDerivedCategory
  rw [← cancel_mono
    ((Functor.mapDerivedCategoryTriangleIso (upperStarComp B j b)).hom.app
      (J.mapDerivedCategory.obj K)), Category.assoc, Iso.inv_hom_id_app]
  simp only [Functor.comp_obj, Category.comp_id]
  rw [derived_open_unit B b]
  simp only [Functor.mapDerivedCategoryTriangleIso, openCompanionTriangle,
    Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    Functor.mapDerivedCategoryNatIso_trans, Functor.map_comp, Category.assoc]
  have hl := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft J t.symm) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hl
  rw [reassoc_of% hl]
  simp only [Functor.mapDerivedCategoryNatIso_symm,  Functor.comp_obj]
  erw [Iso.inv_hom_id_app_assoc]
  have hassoc : Functor.associator J R S = Iso.refl (J ⋙ R ⋙ S) := by rfl
  have hunitor : S.leftUnitor.symm = Iso.refl S := by rfl
  have hDa : Functor.mapDerivedCategoryNatIso (Functor.associator J R S) =
      Iso.refl ((J ⋙ R ⋙ S).mapDerivedCategory) := by
    apply Iso.ext
    exact Functor.mapDerivedCategoryNatIso_refl (F := J ⋙ R ⋙ S)
  have hDu : Functor.mapDerivedCategoryNatIso S.leftUnitor =
      Iso.refl S.mapDerivedCategory := by
    apply Iso.ext
    exact Functor.mapDerivedCategoryNatIso_refl (F := S)
  rw [hDa, hDu]
  simp only [Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
  have ha := congr_app (Functor.mapDerivedCategoryCompIso_assoc J R S) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at ha
  erw [Category.id_comp, Category.id_comp]
  rw [ha]
  have hr := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerRight
    (asIso (openImmersionLowerShriekUpperStarAdjunction B b).unit) S) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app] at hr
  rw [reassoc_of% hr]
  have hu := congr_app (Functor.mapDerivedCategoryCompIso_id_comp S) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, NatTrans.id_app] at hu
  have hi : (Functor.mapDerivedCategoryCompIso
      (𝟭 (Sheaf Y.smallEtaleTopology B)) S).inv.app K =
      S.mapDerivedCategory.map
        ((Functor.mapDerivedCategoryIdIso (Sheaf Y.smallEtaleTopology B)).inv.app K) := by
    let e := S.mapDerivedCategory.mapIso
      ((Functor.mapDerivedCategoryIdIso (Sheaf Y.smallEtaleTopology B)).app K)
    apply (cancel_mono e.hom).1
    exact hu.trans e.inv_hom_id.symm
  rw [hi]

omit [HasSmallSiteSheafify B] [UpperStarPreservesFlat B] in
private theorem derived_open_comp_unit
    {X Y Z : Scheme.{u}} (j : X ⟶ Y) (b : Y ⟶ Z)
    [IsOpenImmersion j] [IsOpenImmersion b]
    (M : DerivedCategory (Sheaf X.smallEtaleTopology B)) :
    (derivedOpenImmersionLowerShriekUpperStarAdjunction B (j ≫ b)).unit.app M ≫
        (upperStar B (j ≫ b)).mapDerivedCategory.map
          ((mapDerivedCategoryOpenImmersionLowerShriekComp B j b).hom.app M) =
      (derivedOpenImmersionLowerShriekUpperStarAdjunction B j).unit.app M ≫
        (upperStar B j).mapDerivedCategory.map
          ((derivedOpenImmersionLowerShriekUpperStarAdjunction B b).unit.app
            ((openImmersionLowerShriek B j).mapDerivedCategory.obj M)) ≫
        (Functor.mapDerivedCategoryTriangleIso (upperStarComp B j b)).inv.app
          ((openImmersionLowerShriek B b).mapDerivedCategory.obj
            ((openImmersionLowerShriek B j).mapDerivedCategory.obj M)) := by
  have h := Adjunction.mapDerivedCategoryAdjunction_mate'
    (openImmersionLowerShriekUpperStarAdjunction B j)
    (openImmersionLowerShriekUpperStarAdjunction B (j ≫ b))
    (openCompanionTriangle B j b) (openImmersionLowerShriekComp B j b)
    (open_companion_unit B j b) M
  rw [derived_open_companion] at h
  exact h

end

section

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  leftDerivedUpperStarTensorComparison

omit [HasSmallSiteSheafify B] [UpperStarPreservesFlat B] in
private theorem pullback_comp
    {X Y Z : Scheme.{u}} (j : X ⟶ Y) (b : Y ⟶ Z)
    [IsOpenImmersion j] [IsOpenImmersion b]
    (N : DerivedCategory (Sheaf Z.smallEtaleTopology B)) :
    (leftDerivedUpperStarComp B j b).hom.app N ≫
        (upperStar B j).leftDerivedFunctor.map
          ((leftDerivedUpperStarIsoMapDerivedCategory B b).hom.app N) ≫
        (leftDerivedUpperStarIsoMapDerivedCategory B j).hom.app
          ((upperStar B b).mapDerivedCategory.obj N) =
      (leftDerivedUpperStarIsoMapDerivedCategory B (j ≫ b)).hom.app N ≫
        (Functor.mapDerivedCategoryTriangleIso (upperStarComp B j b)).hom.app N := by
  simp only [leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, leftDerivedUpperStarIsoMapDerivedCategory,
    Functor.mapDerivedCategoryTriangleIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc,
    Iso.inv_hom_id_app_assoc]
  rw [← (upperStar B j).leftDerivedFunctorIsoMapDerivedCategory.inv.naturality_assoc]
  simp only [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.comp_id]
  erw [Category.comp_id]

omit [HasSmallSiteSheafify B] in
private theorem open_tensor_component
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (M N : DerivedCategory (Sheaf Y.smallEtaleTopology B)) :
    ((mapDerivedCategoryUpperStarDerivedTensorIso B j).hom.app M).app N =
      ((derivedTensor B X).map
        ((leftDerivedUpperStarIsoMapDerivedCategory B j).inv.app M)).app
          ((upperStar B j).leftDerivedFunctor.obj N) ≫
        ((leftDerivedUpperStarTensorNatIso B j).inv.app M).app N ≫
        (leftDerivedUpperStarIsoMapDerivedCategory B j).hom.app
          (((derivedTensor B Y).obj M).obj N) := by
  rfl

omit [HasSmallSiteSheafify B] in
private theorem open_tensor_comp
    {X Y Z : Scheme.{u}} (j : X ⟶ Y) (b : Y ⟶ Z)
    [IsOpenImmersion j] [IsOpenImmersion b]
    (M N : DerivedCategory (Sheaf Z.smallEtaleTopology B)) :
    let R := (upperStar B j).mapDerivedCategory
    let S := (upperStar B b).mapDerivedCategory
    let F := (upperStar B j).leftDerivedFunctor
    let G := (upperStar B b).leftDerivedFunctor
    let T := derivedTensor B X
    let U := derivedTensor B Z
    let dc := Functor.mapDerivedCategoryTriangleIso (upperStarComp B j b)
    let lc := leftDerivedUpperStarComp B j b
    ((mapDerivedCategoryUpperStarDerivedTensorIso B j).hom.app (S.obj M)).app
        (G.obj N) ≫
        R.map (((mapDerivedCategoryUpperStarDerivedTensorIso B b).hom.app M).app N) ≫
        dc.inv.app ((U.obj M).obj N) =
      (T.map (dc.inv.app M)).app (F.obj (G.obj N)) ≫
        (T.obj ((upperStar B (j ≫ b)).mapDerivedCategory.obj M)).map (lc.inv.app N) ≫
        ((mapDerivedCategoryUpperStarDerivedTensorIso B (j ≫ b)).hom.app M).app N := by
  let F := (upperStar B j).leftDerivedFunctor
  let R := (upperStar B j).mapDerivedCategory
  let G := (upperStar B b).leftDerivedFunctor
  let S := (upperStar B b).mapDerivedCategory
  let H := (upperStar B (j ≫ b)).leftDerivedFunctor
  let Q := (upperStar B (j ≫ b)).mapDerivedCategory
  let T := derivedTensor B X
  let U := derivedTensor B Y
  let V := derivedTensor B Z
  let lf := leftDerivedUpperStarIsoMapDerivedCategory B j
  let lg := leftDerivedUpperStarIsoMapDerivedCategory B b
  let lh := leftDerivedUpperStarIsoMapDerivedCategory B (j ≫ b)
  let lc := leftDerivedUpperStarComp B j b
  let dc := Functor.mapDerivedCategoryTriangleIso (upperStarComp B j b)
  let cf := leftDerivedUpperStarTensorNatIso B j
  let cg := leftDerivedUpperStarTensorNatIso B b
  let ch := leftDerivedUpperStarTensorNatIso B (j ≫ b)
  let l := Functor.isoWhiskerRight lg F ≪≫ Functor.isoWhiskerLeft S lf
  let cc := (Functor.postcompose₂.obj F).mapIso cg ≪≫
    (((Functor.whiskeringLeft₂ _).obj G).obj G).mapIso cf
  have hl : ∀ P, lc.hom.app P ≫ l.hom.app P = lh.hom.app P ≫ dc.hom.app P := by
    intro P
    simpa only [l, F, S, lf, lg, lh, lc, dc, Functor.mapDerivedCategoryTriangleIso,
      Iso.trans_hom, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, NatTrans.comp_app, Category.assoc] using
      pullback_comp B j b P
  have hc : ∀ P Q', lc.hom.app ((V.obj P).obj Q') ≫ (cc.hom.app P).app Q' =
      (ch.hom.app P).app Q' ≫
        (T.map (lc.hom.app P)).app (H.obj Q') ≫
        (T.obj ((G ⋙ F).obj P)).map (lc.hom.app Q') := by
    intro P Q'
    have h := leftDerivedUpperStarTensorComparison_comp B j b (j ≫ b) rfl P Q'
    rw [MonoidalCategory.tensorHom_def] at h
    simpa only [cc, cf, cg, ch, T, V, F, G, H, lc,
      leftDerivedUpperStarTensorNatIso_hom, derivedTensor,
      MonoidalCategory.curriedTensor_obj_obj, MonoidalCategory.curriedTensor_map_app,
      MonoidalCategory.curriedTensor_obj_map,
      leftDerivedUpperStarDerivedTensor, derivedTensorLeftDerivedUpperStar,
      derivedTensor_map_app, derivedTensor_obj_map,
      Iso.trans_hom, Functor.mapIso_hom, NatTrans.comp_app,
      asIso_hom, Functor.postcompose₂, Functor.whiskeringLeft₂,
      Functor.whiskeringLeft, Functor.whiskeringRight, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.comp_map, Functor.comp_obj, Category.assoc] using h.symm
  have ht := left_tensor_comparison_transport (G ⋙ F) H (S ⋙ R) Q T V
    lc dc l lh cc ch hl hc M N
  have hn := left_tensor_comparison_comp F R G S T U V lf lg cf cg M N
  dsimp only [cc, Iso.trans_inv, Functor.mapIso_inv, NatTrans.comp_app,
    Functor.postcompose₂, Functor.whiskeringLeft₂, Functor.whiskeringLeft,
    Functor.whiskeringRight, Functor.comp_obj, Functor.comp_map] at ht
  simp only [Functor.whiskerLeft_app, Functor.whiskerRight_app,
     Category.assoc] at ht
  dsimp only at hn
  rw [← reassoc_of% hn] at ht
  simpa only [open_tensor_component, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_hom, Functor.whiskeringLeft₂,
    Functor.postcompose₂, Functor.whiskeringLeft, Functor.whiskeringRight,
    NatTrans.comp_app, Functor.comp_obj, Functor.comp_map,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.map_comp, Category.assoc] using ht

end

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor

omit [HasSmallSiteSheafify B] in
/-- The inverse open projection formulas compose through the specified open compositor.
Source: Stacks Project, sites-cohomology Tag 0GL1 and sites-modules Tag 0E8I
(auxiliary; not a blueprint node).

Proof: the sheaf tensor comparison for extension by zero restricts to the identity on
its open and is zero off that open. For two nested opens both compositions therefore
extend the same tensor morphism by zero, with the same adjunction units. This identifies
them through the canonical compositor, which is the comparison of left adjoints of
restriction. Pass to complexes, preserving the direct-sum tensor differential, and use
K-flat representatives for the tensor factors. The exact extension functors and their
composition comparisons descend through quasi-isomorphisms. The canonical derived
pullback compositor supplies precisely the final tensor-factor map displayed below.
Equivalently, transpose through the composite derived open adjunction: the two
transposes are the same composite of pullback tensor comparisons and units. Their
equality follows from composition of units and the monoidal pullback composition law.
Neither boundedness nor finite Tor dimension is used.
-/
theorem derivedOpenImmersionLowerShriekProjectionIso_inv_comp
    {X Y Z : Scheme.{u}} (j : X ⟶ Y) (b : Y ⟶ Z) (a : X ⟶ Z)
    [IsOpenImmersion j] [IsOpenImmersion b] [IsOpenImmersion a]
    (h : j ≫ b = a)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology B))
    (N : DerivedCategory (Sheaf Z.smallEtaleTopology B)) :
    let J := (openImmersionLowerShriek B j).mapDerivedCategory
    let I := (openImmersionLowerShriek B b).mapDerivedCategory
    let A := (openImmersionLowerShriek B a).mapDerivedCategory
    let E := (mapDerivedCategoryOpenImmersionLowerShriekComp B j b).symm ≪≫
      mapDerivedCategoryOpenImmersionLowerShriekCongr B h
    let L := (upperStar B b).leftDerivedFunctor
    let T := derivedTensor B X
    let U := derivedTensor B Z
    (U.map (E.hom.app M)).app N ≫
        ((derivedOpenImmersionLowerShriekProjectionIso B a).inv.app M).app N ≫
        A.map ((T.obj M).map ((leftDerivedUpperStarComp B j b a h.symm).hom.app N)) =
      ((derivedOpenImmersionLowerShriekProjectionIso B b).inv.app (J.obj M)).app N ≫
        I.map (((derivedOpenImmersionLowerShriekProjectionIso B j).inv.app M).app (L.obj N)) ≫
        E.hom.app ((T.obj M).obj ((upperStar B j).leftDerivedFunctor.obj (L.obj N))) := by
  subst a
  let J := (openImmersionLowerShriek B j).mapDerivedCategory
  let I := (openImmersionLowerShriek B b).mapDerivedCategory
  let A := (openImmersionLowerShriek B (j ≫ b)).mapDerivedCategory
  let R := (upperStar B j).mapDerivedCategory
  let S := (upperStar B b).mapDerivedCategory
  let Q := (upperStar B (j ≫ b)).mapDerivedCategory
  let Lj := (upperStar B j).leftDerivedFunctor
  let Lb := (upperStar B b).leftDerivedFunctor
  let Lh := (upperStar B (j ≫ b)).leftDerivedFunctor
  let T := derivedTensor B X
  let U := derivedTensor B Y
  let V := derivedTensor B Z
  let dj := (mapDerivedCategoryUpperStarDerivedTensorIso B j).hom
  let db := (mapDerivedCategoryUpperStarDerivedTensorIso B b).hom
  let dh := (mapDerivedCategoryUpperStarDerivedTensorIso B (j ≫ b)).hom
  let dc : (((Functor.whiskeringLeft₂ _).obj (S ⋙ R)).obj (Lb ⋙ Lj)).obj T ⟶
      (Functor.postcompose₂.obj (S ⋙ R)).obj V :=
    (((Functor.whiskeringLeft₂ _).obj S).obj Lb).map dj ≫
    (Functor.postcompose₂.obj R).map db
  let lc := leftDerivedUpperStarComp B j b
  let rc := Functor.mapDerivedCategoryTriangleIso (upperStarComp B j b)
  let ec := mapDerivedCategoryOpenImmersionLowerShriekComp B j b
  have hp := Adjunction.projectionMap_mate
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction B j).comp
      (derivedOpenImmersionLowerShriekUpperStarAdjunction B b))
    (derivedOpenImmersionLowerShriekUpperStarAdjunction B (j ≫ b))
    (Lb ⋙ Lj) Lh (T₁ := T) (T'₁ := V) (T₂ := T) (T'₂ := V)
    dc dh (U := 𝟭 _) (V := 𝟭 _) (𝟙 _) (𝟙 _)
    rc.inv lc.inv ec.hom (fun P ↦ by
      simp only [Adjunction.comp_unit_app, Functor.id_obj, Functor.id_map, Functor.comp_obj]
      simpa only [Category.assoc] using derived_open_comp_unit B j b P)
    (fun P Q' ↦ by
      simpa only [dc, dj, db, dh, R, S, Q, Lj, Lb, T, V, lc, rc,
        NatTrans.comp_app, Functor.id_obj, Functor.id_map, NatTrans.id_app,
        Functor.whiskeringLeft₂, Functor.postcompose₂, Functor.whiskeringLeft,
        Functor.whiskeringRight, Functor.comp_map, Functor.comp_obj,
        Functor.whiskerLeft_app, Functor.whiskerRight_app,
        CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id, Category.assoc]
        using open_tensor_comp B j b P Q') M N
  have hc := left_projection_comp
    (derivedOpenImmersionLowerShriekUpperStarAdjunction B j)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction B b)
    Lj Lb T U V dj db M N
  dsimp only at hc
  rw [hc] at hp
  simp only [Functor.id_obj, Functor.id_map, NatTrans.id_app,
    Functor.postcompose₂, Functor.whiskeringRight, Functor.comp_obj,
    CategoryTheory.Functor.map_id, Category.id_comp,  Category.assoc] at hp
  erw [Category.comp_id] at hp
  change ec.hom.app ((T.obj M).obj (Lj.obj (Lb.obj N))) ≫
      I.map (((derivedOpenImmersionLowerShriekProjectionIso B j).hom.app M).app
        (Lb.obj N)) ≫
      ((derivedOpenImmersionLowerShriekProjectionIso B b).hom.app (J.obj M)).app N =
    A.map ((T.obj M).map (lc.inv.app N)) ≫
      ((derivedOpenImmersionLowerShriekProjectionIso B (j ≫ b)).hom.app M).app N ≫
      (V.map (ec.hom.app M)).app N at hp
  have hi := inverse_congr hp
  simp only [IsIso.inv_comp, ← Functor.map_inv, inv_bifunctor_component, NatIso.inv_hom_app,
    NatIso.inv_inv_app] at hi
  have ht := NatIso.inv_map_hom_app V (ec.app M) N
  simp only [Iso.app_hom, Iso.app_inv] at ht
  rw [ht] at hi
  simpa only [mapDerivedCategoryOpenImmersionLowerShriekCongr, Iso.trans_hom,
    Iso.symm_hom, Iso.refl_hom, NatTrans.comp_app, NatTrans.id_app,
    Category.comp_id, Category.assoc] using hi.symm

end AlgebraicGeometry.Etale
