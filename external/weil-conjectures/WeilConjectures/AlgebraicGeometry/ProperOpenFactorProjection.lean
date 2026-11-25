/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import all WeilConjectures.AlgebraicGeometry.CompactificationProjectionComposition
import all WeilConjectures.AlgebraicGeometry.OpenImmersionProjectionComposition
import all WeilConjectures.AlgebraicGeometry.SfEtaleGraphTransferTensor

/-! # Projection for a proper morphism factored through an open

Source: Stacks Project, Tags 0F7B, 0GL1 and 0B56.
The generic coefficient calculations keep the derived-category instance certificates
as parameters, so the kernel checks the specializations without expanding their constructions.
-/

@[expose] public section

set_option autoImplicit false
-- Preserve sharing of the derived-category instances in local functor definitions.
set_option cleanup.letToHave false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true

universe u u'

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

-- Match the braidings used by the generic derived-tensor comparisons.
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] Etale.sheafBraidedCategory

private theorem inverse_comparison
    {C : Type*} [Category C] {X Y Z : C}
    {a : X ⟶ Y} {b : Y ⟶ X} {c : Y ⟶ Z} {d : X ⟶ Z}
    (hi : b ≫ a = 𝟙 Y) (h : a ≫ c = d) : b ≫ d = c := by
  rw [← h, ← Category.assoc, hi, Category.id_comp]

private theorem identity_mixed_paste
    {C : Type*} [Category C] (T : C ⥤ C ⥤ C)
    {M PM FM FN U FU PU : C}
    (a : M ⟶ PM) (b : PM ⟶ FM) (d : FM ≅ M)
    (c : (T.obj FM).obj FN ⟶ FU) (l : FU ⟶ PU) (e : PU ≅ U)
    (t : (T.obj M).obj FN ⟶ U)
    (hm : a ≫ b = d.inv)
    (ht : c ≫ l ≫ e.hom = (T.map d.hom).app FN ≫ t) :
    (T.map a).app FN ≫ (T.map b).app FN ≫ c ≫ l = t ≫ e.inv := by
  have hm' : (T.map a).app FN ≫ (T.map b).app FN = (T.map d.inv).app FN := by
    rw [← NatTrans.comp_app, ← T.map_comp, hm]
  apply (cancel_mono e.hom).1
  simp only [Category.assoc, e.inv_hom_id, Category.comp_id]
  rw [reassoc_of% hm', ht]
  rw [← Category.assoc, ← NatTrans.comp_app, ← T.map_comp, d.inv_hom_id,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]

attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian

attribute [local irreducible] Functor.mapDerivedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor upperStar lowerStar
  openImmersionLowerShriek leftDerivedUpperStarComp leftDerivedUpperStarId
  leftDerivedUpperStarTensorComparison leftDerivedUpperStarTensorNatIso
  mapDerivedCategoryUpperStarDerivedTensorIso leftDerivedUpperStarIsoMapDerivedCategory
  Functor.mapDerivedCategoryNatIso

attribute [local instance] Sheaf.monoidalCategory

private theorem identity_tensor_normalization
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (M N : DerivedCategoryModule A X) :
    let B := ModuleCat.{u + 1} A
    let F := (upperStar B (𝟙 X)).leftDerivedFunctor
    let e := leftDerivedUpperStarId B X
    ((leftDerivedUpperStarTensorComparison B (𝟙 X)).app M).app N ≫
      ((derivedTensor B X).map (e.hom.app M)).app (F.obj N) ≫
        ((derivedTensor B X).obj M).map (e.hom.app N) =
      e.hom.app (((derivedTensor B X).obj M).obj N) := by
  simpa only [leftDerivedUpperStarTensorIso_hom, MonoidalCategory.tensorHom_def,
    derivedTensor, curriedTensor_map_app, curriedTensor_obj_map,
    curriedTensor_obj_obj, Functor.id_obj] using
    identity_pullback_tensor A X M N

attribute [local implicit_reducible] derivedTensorRightDerivedLowerStar
  rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar

attribute [local irreducible] derivedTensor rightDerivedLowerStarProjectionMap
  derivedOpenImmersionLowerShriekProjectionIso openImmersionLowerShriekLowerStarExchange

private theorem identity_unit
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (M : DerivedCategoryModule A X) :
    let B := ModuleCat.{u + 1} A
    let P := (upperStar B (𝟙 X)).mapDerivedCategory
    let d := mapDerivedCategoryOpenImmersionLowerShriekId B X
    let e := Functor.mapDerivedCategoryNatIso (upperStarId B X) ≪≫
      Functor.mapDerivedCategoryIdIso _
    (derivedOpenImmersionLowerShriekUpperStarAdjunction B (𝟙 X)).unit.app M ≫
      P.map (d.hom.app M) ≫ e.hom.app M = 𝟙 _ := by
  let B := ModuleCat.{u + 1} A
  let J := openImmersionLowerShriek B (𝟙 X)
  let P := upperStar B (𝟙 X)
  let d := openImmersionLowerShriekId B X
  let e := upperStarId B X
  let adj := openImmersionLowerShriekUpperStarAdjunction B (𝟙 X)
  have ho : asIso adj.unit ≪≫ Functor.isoWhiskerRight d P ≪≫ e = Iso.refl (𝟭 _) := by
    apply Iso.ext
    apply NatTrans.ext
    funext Z
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, asIso_hom, Iso.refl_hom, NatTrans.id_app]
    have hh := Adjunction.unit_leftAdjointUniq_hom_app adj
      (Adjunction.id.ofNatIsoRight e.symm) Z
    simp only [Adjunction.ofNatIsoRight_unit, Adjunction.id_unit,
      Category.id_comp, Iso.symm_hom] at hh
    change adj.unit.app Z ≫ P.map (d.hom.app Z) = e.inv.app Z at hh
    rw [← Category.assoc, hh, e.inv_hom_id_app]
  have hd := congrArg (fun z ↦ (Functor.mapDerivedCategoryNatIso z).hom.app M) ho
  simp only [Functor.mapDerivedCategoryNatIso_trans,
    Functor.mapDerivedCategoryNatIso_refl, NatTrans.comp_app, NatTrans.id_app] at hd
  have hw := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerRight d P) M
  have hc := congr_app (Functor.mapDerivedCategoryCompIso_id_comp P) M
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app] at hw hc
  dsimp only
  rw [derived_open_unit B (𝟙 X)]
  simp only [mapDerivedCategoryOpenImmersionLowerShriekId, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hw, reassoc_of% hc]
  simp only [NatTrans.id_app]
  erw [Category.id_comp, reassoc_of% hd]
  simp only [Iso.inv_hom_id_app]

private theorem identity_left_to_map
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (M : DerivedCategoryModule A X) :
    (leftDerivedUpperStarId (ModuleCat.{u + 1} A) X).hom.app M =
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) (𝟙 X)).hom.app M ≫
        (Functor.mapDerivedCategoryNatIso (upperStarId (ModuleCat.{u + 1} A) X)).hom.app M ≫
        (Functor.mapDerivedCategoryIdIso _).hom.app M := by
  simp only [leftDerivedUpperStarId, Functor.leftDerivedFunctorNatIso,
    leftDerivedUpperStarIsoMapDerivedCategory, Iso.trans_hom, NatTrans.comp_app,
    Iso.symm_hom, Category.assoc, Iso.inv_hom_id_app_assoc]

private theorem generic_identity_mixed_tensor
    (B : Type u') [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B]
    [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [UpperStarPreservesFlat B]
    {FC : B → B → Type*} {CC : B → Type (u + 1)}
    [∀ (P Q : B), FunLike (FC P Q) (CC P) (CC Q)]
    [ConcreteCategory.{u + 1} B FC]
    [(CategoryTheory.forget B).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget B)]
    [∀ (Z : Scheme.{u}), Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget B)]
    (X : Scheme.{u})
    (M N : DerivedCategory (Sheaf X.smallEtaleTopology B))
    (hleft : ∀ Z : DerivedCategory (Sheaf X.smallEtaleTopology B),
      (leftDerivedUpperStarId B X).hom.app Z =
        (leftDerivedUpperStarIsoMapDerivedCategory B (𝟙 X)).hom.app Z ≫
          (Functor.mapDerivedCategoryNatIso (upperStarId B X)).hom.app Z ≫
          (Functor.mapDerivedCategoryIdIso _).hom.app Z)
    (htensor :
      ((leftDerivedUpperStarTensorComparison B (𝟙 X)).app M).app N ≫
        ((derivedTensor B X).map ((leftDerivedUpperStarId B X).hom.app M)).app
          ((upperStar B (𝟙 X)).leftDerivedFunctor.obj N) ≫
        ((derivedTensor B X).obj M).map ((leftDerivedUpperStarId B X).hom.app N) =
      (leftDerivedUpperStarId B X).hom.app (((derivedTensor B X).obj M).obj N)) :
    let F := (upperStar B (𝟙 X)).leftDerivedFunctor
    let e := Functor.mapDerivedCategoryNatIso (upperStarId B X) ≪≫
      Functor.mapDerivedCategoryIdIso _
    ((derivedTensor B X).map (e.inv.app M)).app (F.obj N) ≫
      ((mapDerivedCategoryUpperStarDerivedTensorIso B (𝟙 X)).hom.app M).app N =
        ((derivedTensor B X).obj M).map ((leftDerivedUpperStarId B X).hom.app N) ≫
          e.inv.app (((derivedTensor B X).obj M).obj N) := by
  let T := derivedTensor B X
  let F := (upperStar B (𝟙 X)).leftDerivedFunctor
  let l := leftDerivedUpperStarIsoMapDerivedCategory B (𝟙 X)
  let e := Functor.mapDerivedCategoryNatIso (upperStarId B X) ≪≫
    Functor.mapDerivedCategoryIdIso _
  let d := leftDerivedUpperStarId B X
  have hl : l ≪≫ e = d := by
    apply Iso.ext
    apply NatTrans.ext
    funext Z
    exact (hleft Z).symm
  have hli : e.inv.app M ≫ l.inv.app M = d.inv.app M := by
    simpa only [Iso.trans_inv, NatTrans.comp_app] using
      congrArg (fun z ↦ z.inv.app M) hl
  have hlh : l.hom.app (((T.obj M).obj N)) ≫ e.hom.app (((T.obj M).obj N)) =
      d.hom.app (((T.obj M).obj N)) := by
    exact congrArg (fun z ↦ z.hom.app (((T.obj M).obj N))) hl
  have hd : ((leftDerivedUpperStarTensorNatIso B (𝟙 X)).inv.app M).app N ≫
      d.hom.app (((T.obj M).obj N)) =
        (T.map (d.hom.app M)).app (F.obj N) ≫ (T.obj M).map (d.hom.app N) := by
    exact inverse_comparison
      (Iso.inv_hom_id_app_app (leftDerivedUpperStarTensorNatIso B (𝟙 X)) M N)
      (by simpa only [leftDerivedUpperStarTensorNatIso_hom, Category.assoc] using
        htensor)
  have ht : ((leftDerivedUpperStarTensorNatIso B (𝟙 X)).inv.app M).app N ≫
      l.hom.app ((T.obj M).obj N) ≫ e.hom.app ((T.obj M).obj N) =
        (T.map (d.hom.app M)).app (F.obj N) ≫ (T.obj M).map (d.hom.app N) := by
    rw [hlh]
    exact hd
  have hh := identity_mixed_paste T (e.inv.app M) (l.inv.app M) (d.app M)
    (((leftDerivedUpperStarTensorNatIso B (𝟙 X)).inv.app M).app N)
    (l.hom.app ((T.obj M).obj N)) (e.app ((T.obj M).obj N))
    ((T.obj M).map (d.hom.app N)) hli ht
  dsimp only [Functor.postcompose₂, Functor.whiskeringLeft₂,
    Functor.whiskeringLeft, Functor.whiskeringRight, Functor.comp_obj, Functor.id_obj]
  simpa only [open_tensor_component, Category.assoc, Iso.app_inv, Functor.id_obj,
    Functor.comp_obj] using hh

private theorem identity_mixed_tensor
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (M N : DerivedCategoryModule A X) :
    let B := ModuleCat.{u + 1} A
    let F := (upperStar B (𝟙 X)).leftDerivedFunctor
    let e := Functor.mapDerivedCategoryNatIso (upperStarId B X) ≪≫
      Functor.mapDerivedCategoryIdIso _
    ((derivedTensor B X).map (e.inv.app M)).app (F.obj N) ≫
      ((mapDerivedCategoryUpperStarDerivedTensorIso B (𝟙 X)).hom.app M).app N =
        ((derivedTensor B X).obj M).map ((leftDerivedUpperStarId B X).hom.app N) ≫
          e.inv.app (((derivedTensor B X).obj M).obj N) := by
  exact generic_identity_mixed_tensor (ModuleCat.{u + 1} A) X M N
    (identity_left_to_map A X) (identity_tensor_normalization A X M N)

private theorem generic_identity_open_projection
    (B : Type u') [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B]
    [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [UpperStarPreservesFlat B]
    {FC : B → B → Type*} {CC : B → Type (u + 1)}
    [∀ (P Q : B), FunLike (FC P Q) (CC P) (CC Q)]
    [ConcreteCategory.{u + 1} B FC]
    [(CategoryTheory.forget B).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget B)]
    [∀ (Z : Scheme.{u}), Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget B)]
    (X : Scheme.{u})
    (M N : DerivedCategory (Sheaf X.smallEtaleTopology B))
    (hunit : ∀ Z : DerivedCategory (Sheaf X.smallEtaleTopology B),
      (derivedOpenImmersionLowerShriekUpperStarAdjunction B (𝟙 X)).unit.app Z ≫
        (upperStar B (𝟙 X)).mapDerivedCategory.map
          ((mapDerivedCategoryOpenImmersionLowerShriekId B X).hom.app Z) ≫
        (Functor.mapDerivedCategoryNatIso (upperStarId B X) ≪≫
          Functor.mapDerivedCategoryIdIso _).hom.app Z = 𝟙 _)
    (hmixed :
      ((derivedTensor B X).map
        ((Functor.mapDerivedCategoryNatIso (upperStarId B X) ≪≫
          Functor.mapDerivedCategoryIdIso _).inv.app M)).app
          ((upperStar B (𝟙 X)).leftDerivedFunctor.obj N) ≫
        ((mapDerivedCategoryUpperStarDerivedTensorIso B (𝟙 X)).hom.app M).app N =
      ((derivedTensor B X).obj M).map ((leftDerivedUpperStarId B X).hom.app N) ≫
        (Functor.mapDerivedCategoryNatIso (upperStarId B X) ≪≫
          Functor.mapDerivedCategoryIdIso _).inv.app (((derivedTensor B X).obj M).obj N)) :
    let J := (openImmersionLowerShriek B (𝟙 X)).mapDerivedCategory
    let d := mapDerivedCategoryOpenImmersionLowerShriekId B X
    ((derivedOpenImmersionLowerShriekProjectionIso B (𝟙 X)).inv.app M).app N ≫
      J.map (((derivedTensor B X).obj M).map ((leftDerivedUpperStarId B X).hom.app N)) ≫
      d.hom.app (((derivedTensor B X).obj M).obj N) =
        ((derivedTensor B X).map (d.hom.app M)).app N := by
  let J := (openImmersionLowerShriek B (𝟙 X)).mapDerivedCategory
  let P := (upperStar B (𝟙 X)).mapDerivedCategory
  let F := (upperStar B (𝟙 X)).leftDerivedFunctor
  let T := derivedTensor B X
  let d := mapDerivedCategoryOpenImmersionLowerShriekId B X
  let e := Functor.mapDerivedCategoryNatIso (upperStarId B X) ≪≫
    Functor.mapDerivedCategoryIdIso _
  let adj := derivedOpenImmersionLowerShriekUpperStarAdjunction B (𝟙 X)
  let t := (T.obj M).map ((leftDerivedUpperStarId B X).hom.app N)
  have hu (Z : DerivedCategory (Sheaf X.smallEtaleTopology B)) :
      adj.unit.app Z ≫ P.map (d.hom.app Z) = e.inv.app Z := by
    apply (cancel_mono (e.hom.app Z)).1
    simpa only [Category.assoc, e.inv_hom_id_app] using hunit Z
  have hh : J.map t ≫ d.hom.app (((T.obj M).obj N)) =
      ((derivedOpenImmersionLowerShriekProjectionIso B (𝟙 X)).hom.app M).app N ≫
        (T.map (d.hom.app M)).app N := by
    apply (adj.homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    simp only [Functor.map_comp]
    have ht := adj.unit.naturality t
    dsimp only [Functor.comp_map, Functor.id_map] at ht
    rw [← reassoc_of% ht, hu]
    rw [derivedOpenImmersionLowerShriekProjectionIso_hom,
      derivedOpenImmersionLowerShriekProjectionMap]
    have hp := adj.unit_app_comp_map_projectionMap_app_app F T T
      (mapDerivedCategoryUpperStarDerivedTensorIso B (𝟙 X)).hom M N
    erw [reassoc_of% hp]
    simp only [Adjunction.projectionMapTranspose_app_app]
    have hn := congr_app
      ((mapDerivedCategoryUpperStarDerivedTensorIso B (𝟙 X)).hom.naturality
        (d.hom.app M)) N
    dsimp only [Functor.postcompose₂, Functor.whiskeringLeft₂,
      Functor.whiskeringLeft, Functor.whiskeringRight, Functor.comp_map,
      Functor.comp_obj, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.id_obj] at hn
    simp only [Category.assoc]
    erw [← hn]
    erw [← NatTrans.comp_app_assoc, ← T.map_comp, hu]
    exact hmixed.symm
  change ((derivedOpenImmersionLowerShriekProjectionIso B (𝟙 X)).inv.app M).app N ≫
    J.map t ≫ d.hom.app (((T.obj M).obj N)) = (T.map (d.hom.app M)).app N
  rw [hh, Iso.inv_hom_id_app_app_assoc]
private theorem identity_open_projection
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (M N : DerivedCategoryModule A X) :
    let B := ModuleCat.{u + 1} A
    let J := (openImmersionLowerShriek B (𝟙 X)).mapDerivedCategory
    let d := mapDerivedCategoryOpenImmersionLowerShriekId B X
    ((derivedOpenImmersionLowerShriekProjectionIso B (𝟙 X)).inv.app M).app N ≫
      J.map (((derivedTensor B X).obj M).map ((leftDerivedUpperStarId B X).hom.app N)) ≫
      d.hom.app (((derivedTensor B X).obj M).obj N) =
        ((derivedTensor B X).map (d.hom.app M)).app N := by
  exact generic_identity_open_projection (ModuleCat.{u + 1} A) X M N
    (identity_unit A X) (identity_mixed_tensor A X M N)

private theorem generic_factor_full
    (B : Type u') [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B]
    [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [UpperStarPreservesFlat B]
    {FC : B → B → Type*} {CC : B → Type (u + 1)}
    [∀ (P Q : B), FunLike (FC P Q) (CC P) (CC Q)]
    [ConcreteCategory.{u + 1} B FC]
    [(CategoryTheory.forget B).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget B)]
    [∀ (Z : Scheme.{u}), Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget B)]
    {X V U : Scheme.{u}} (s : X ⟶ V) (j : V ⟶ U) (h : X ⟶ U)
    [IsOpenImmersion j] [IsProper h] (fac : s ≫ j = h)
    (E : (lowerStar B s).rightDerivedFunctor ⋙
      (openImmersionLowerShriek B j).mapDerivedCategory ≅
      (lowerStar B h).rightDerivedFunctor)
    (hE : ∀ Z : DerivedCategory (Sheaf X.smallEtaleTopology B),
      E.hom.app Z =
        (openImmersionLowerShriekLowerStarExchange B
          (IsPullback.of_vert_isIso_mono (snd := 𝟙 X) ⟨by simp [fac]⟩)).app Z ≫
        (lowerStar B h).rightDerivedFunctor.map
          ((mapDerivedCategoryOpenImmersionLowerShriekId B X).hom.app Z))
    (hId : ∀ (M N : DerivedCategory (Sheaf X.smallEtaleTopology B)),
      ((derivedOpenImmersionLowerShriekProjectionIso B (𝟙 X)).inv.app M).app N ≫
        (openImmersionLowerShriek B (𝟙 X)).mapDerivedCategory.map
          (((derivedTensor B X).obj M).map ((leftDerivedUpperStarId B X).hom.app N)) ≫
        (mapDerivedCategoryOpenImmersionLowerShriekId B X).hom.app
          (((derivedTensor B X).obj M).obj N) =
      ((derivedTensor B X).map
        ((mapDerivedCategoryOpenImmersionLowerShriekId B X).hom.app M)).app N)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology B))
    (N : DerivedCategory (Sheaf U.smallEtaleTopology B)) :
    ((derivedTensor B U).map (E.hom.app M)).app N ≫
        ((rightDerivedLowerStarProjectionMap B h).app M).app N ≫
        (lowerStar B h).rightDerivedFunctor.map
          (((derivedTensor B X).obj M).map
            ((leftDerivedUpperStarComp B s j h fac.symm).hom.app N)) =
      ((derivedOpenImmersionLowerShriekProjectionIso B j).inv.app
        ((lowerStar B s).rightDerivedFunctor.obj M)).app N ≫
        (openImmersionLowerShriek B j).mapDerivedCategory.map
          (((rightDerivedLowerStarProjectionMap B s).app M).app
            ((upperStar B j).leftDerivedFunctor.obj N)) ≫
        E.hom.app (((derivedTensor B X).obj M).obj
          ((upperStar B s).leftDerivedFunctor.obj
            ((upperStar B j).leftDerivedFunctor.obj N))) := by
  subst h
  let H := (lowerStar B (s ≫ j)).rightDerivedFunctor
  let J := (openImmersionLowerShriek B (𝟙 X)).mapDerivedCategory
  let T := (derivedTensor B X).obj M
  let L := (upperStar B (s ≫ j)).leftDerivedFunctor
  let d := mapDerivedCategoryOpenImmersionLowerShriekId B X
  let e := leftDerivedUpperStarId B X
  let sq : IsPullback s (𝟙 X) j (s ≫ j) :=
    IsPullback.of_vert_isIso_mono ⟨by simp⟩
  let ex := openImmersionLowerShriekLowerStarExchange B sq
  let w := (derivedSquareUpperStarIso B sq.toCommSq).hom.app N
  let c := (leftDerivedUpperStarComp B s j).hom.app N
  have he : e.inv.app (L.obj N) =
      (leftDerivedUpperStarComp B (𝟙 X) (s ≫ j) (s ≫ j)
        (Category.id_comp _).symm).hom.app N := by
    apply (cancel_mono (e.hom.app (L.obj N))).1
    rw [e.inv_hom_id_app, leftDerivedUpperStarComp_id_left_hom_app]
    rfl
  have hw : e.inv.app (L.obj N) ≫ w = c := by
    dsimp only [w, derivedSquareUpperStarIso, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app]
    rw [he, Iso.hom_inv_id_app_assoc]
  have hid : ((derivedOpenImmersionLowerShriekProjectionIso B (𝟙 X)).inv.app M).app
      (L.obj N) ≫ d.hom.app (T.obj ((upperStar B (𝟙 X)).leftDerivedFunctor.obj
        (L.obj N))) =
      ((derivedTensor B X).map (d.hom.app M)).app (L.obj N) ≫
        T.map (e.inv.app (L.obj N)) := by
    apply (cancel_mono (T.map (e.hom.app (L.obj N)))).1
    have hd := d.hom.naturality (T.map (e.hom.app (L.obj N)))
    dsimp only [Functor.comp_map, Functor.id_map] at hd
    simp only [Category.assoc]
    rw [← hd]
    erw [hId M (L.obj N)]
    simp only [← T.map_comp, e.inv_hom_id_app]
    erw [T.map_id, Category.comp_id]
  have h0 := (mixed_projection B sq M N).symm
  have h1 := congrArg (fun z ↦ z ≫ H.map (d.hom.app (T.obj
    ((upperStar B s).leftDerivedFunctor.obj
      ((upperStar B j).leftDerivedFunctor.obj N))))) h0
  simp only [Category.assoc] at h1
  have hd := d.hom.naturality (T.map w)
  dsimp only [Functor.comp_map, Functor.id_map] at hd
  have hdH := congrArg H.map hd
  simp only [Functor.map_comp] at hdH
  erw [hdH] at h1
  have hiH := congrArg H.map hid
  simp only [Functor.map_comp] at hiH
  erw [reassoc_of% hiH] at h1
  have hc : H.map (T.map (e.inv.app (L.obj N))) ≫ H.map (T.map w) =
      H.map (T.map c) := by
    rw [← H.map_comp, ← T.map_comp, hw]
  erw [hc] at h1
  change ((derivedTensor B U).map (E.hom.app M)).app N ≫
      ((rightDerivedLowerStarProjectionMap B (s ≫ j)).app M).app N ≫
      H.map (T.map c) = _
  rw [hE M, hE]
  simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]
  erw [rightDerivedLowerStarProjectionMap_naturality_left_assoc B (s ≫ j)
    (d.hom.app M) N]
  exact h1

/-- The identity-top specialization of the proper/open projection square.

Source: Stacks Project, Tags 0F7B, 0GL1 and 0B56
(auxiliary; not a blueprint node).

Proof in words. The square with arrows h', identity, u, h is Cartesian, since u
is a monomorphism and h' u = h. Apply the proper/open tensor square to it.
Remove extension by the identity using its canonical identity comparison. The
open identity projection becomes the tensor of that comparison and the inverse
of the canonical pullback identity comparison. The identity-top square pullback
comparison followed by this pullback identity is the h',u composition comparison.
Naturality of the proper projection and of the identity comparison then gives
the displayed square. All these maps are the specified unit/counit maps; no
proper projection is inverted.
-/
theorem properOpenFactor_projection
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X V U : Scheme.{u}} (s : X ⟶ V) (j : V ⟶ U) (h : X ⟶ U)
    [IsOpenImmersion j] [IsProper h] (fac : s ≫ j = h)
    (M : DerivedCategoryModule A X) (N : DerivedCategoryModule A U) :
    let B := ModuleCat.{u + 1} A
    let E := rightDerivedLowerStarCompOpenImmersionLowerShriekIso A s j h fac
    ((derivedTensor B U).map (E.hom.app M)).app N ≫
        ((rightDerivedLowerStarProjectionMap B h).app M).app N ≫
        (lowerStar B h).rightDerivedFunctor.map
          (((derivedTensor B X).obj M).map
            ((leftDerivedUpperStarComp B s j h fac.symm).hom.app N)) =
      ((derivedOpenImmersionLowerShriekProjectionIso B j).inv.app
        ((lowerStar B s).rightDerivedFunctor.obj M)).app N ≫
        (openImmersionLowerShriek B j).mapDerivedCategory.map
          (((rightDerivedLowerStarProjectionMap B s).app M).app
            ((upperStar B j).leftDerivedFunctor.obj N)) ≫
        E.hom.app (((derivedTensor B X).obj M).obj
          ((upperStar B s).leftDerivedFunctor.obj
            ((upperStar B j).leftDerivedFunctor.obj N))) := by
  apply generic_factor_full (ModuleCat.{u + 1} A) s j h fac
    (rightDerivedLowerStarCompOpenImmersionLowerShriekIso A s j h fac)
    ?_ (identity_open_projection A X) M N
  intro Z
  simp only [rightDerivedLowerStarCompOpenImmersionLowerShriekIso,
    Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    openImmersionLowerShriekLowerStarExchangeIso, asIso_hom]
  erw [Category.comp_id]

end AlgebraicGeometry.Etale
