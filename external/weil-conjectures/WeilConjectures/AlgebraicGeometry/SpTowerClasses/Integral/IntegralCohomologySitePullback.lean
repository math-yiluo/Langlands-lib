/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Integral.IntegralSitePullbackEndpoints
public import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnityPullback
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-! # Exact-derived transport through the etale-to-pro-etale square

Source: blueprint chap-Smooth-purity, classes proof (2).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄ w₁ w₂ w₃ w₄ t₁ t₂ t₃ t₄

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [local irreducible] Functor.mapDerivedCategory lineBundleEtaleClass lineBundleClass
attribute [local irreducible] mapSingleArrow mapExtensionEndpoints

private theorem mapSingleArrow_comp_iso
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    {E : Type u₃} [Category.{v₃} E] [Abelian E]
    [HasDerivedCategory.{t₁} C] [HasDerivedCategory.{t₂} D] [HasDerivedCategory.{t₃} E]
    [HasExt.{w₁} C] [HasExt.{w₂} D] [HasExt.{w₃} E] [EnoughInjectives C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : D ⥤ E) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (H : C ⥤ E) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (τ : H ≅ F ⋙ G) {A B : C} (e : Ext.{w₁} A B 1) :
    mapSingleArrow G 1 (mapSingleArrow F 1 e.hom) =
      (DerivedCategory.singleFunctor E 0).map (τ.inv.app A) ≫
        mapSingleArrow H 1 e.hom ≫
        ((DerivedCategory.singleFunctor E 0).map (τ.hom.app B))⟦(1 : ℤ)⟧' := by
  have h := congrArg (fun x : Ext.{w₃} (G.obj (F.obj A)) (G.obj (F.obj B)) 1 ↦
      (show (DerivedCategory.singleFunctor E 0).obj (G.obj (F.obj A)) ⟶
        ((DerivedCategory.singleFunctor E 0).obj (G.obj (F.obj B)))⟦(1 : ℤ)⟧ from x.hom))
    (Ext.mapExactFunctor_mapExactFunctor_of_iso F G H τ e)
  simp only [Ext.mapExactFunctor_hom, Ext.comp_hom, Ext.mk₀_hom,
    ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀, ShiftedHom.map,
    Int.natCast_one, Category.assoc] at h
  simpa only [mapSingleArrow, Category.assoc] using h

private theorem mapSingleArrow_precomp
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    [HasDerivedCategory.{t₁} C] [HasDerivedCategory.{t₂} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {A A' B : C} (a : A' ⟶ A)
    (h : (DerivedCategory.singleFunctor C 0).obj A ⟶
      ((DerivedCategory.singleFunctor C 0).obj B)⟦(1 : ℤ)⟧) :
    mapSingleArrow F 1 ((DerivedCategory.singleFunctor C 0).map a ≫ h) =
      (DerivedCategory.singleFunctor D 0).map (F.map a) ≫ mapSingleArrow F 1 h := by
  simp only [mapSingleArrow, Functor.map_comp, Category.assoc]
  have hn := (F.mapDerivedCategorySingleFunctor 0).inv.naturality a
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]

private theorem mapSingleArrow_postcomp
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    [HasDerivedCategory.{t₁} C] [HasDerivedCategory.{t₂} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {A B B' : C} (b : B ⟶ B')
    (h : (DerivedCategory.singleFunctor C 0).obj A ⟶
      ((DerivedCategory.singleFunctor C 0).obj B)⟦(1 : ℤ)⟧) :
    mapSingleArrow F 1 (h ≫ ((DerivedCategory.singleFunctor C 0).map b)⟦(1 : ℤ)⟧') =
      mapSingleArrow F 1 h ≫
        ((DerivedCategory.singleFunctor D 0).map (F.map b))⟦(1 : ℤ)⟧' := by
  simp only [mapSingleArrow, Functor.map_comp, Category.assoc]
  rw [Functor.commShiftIso_hom_naturality_assoc]
  have hn := (F.mapDerivedCategorySingleFunctor 0).hom.naturality b
  dsimp only [Functor.comp_map] at hn
  rw [← Functor.map_comp, hn, Functor.map_comp]

private theorem mapExtensionEndpoints_hom
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    [HasDerivedCategory.{t₁} C] [HasDerivedCategory.{t₂} D]
    [HasExt.{w₁} C] [HasExt.{w₂} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {A B : C} {A' B' : D} (e : Ext.{w₁} A B 1)
    (z : A' ⟶ F.obj A) (a : F.obj B ⟶ B') :
    (((Ext.mk₀ z).comp (e.mapExactFunctor F) (zero_add 1)).comp
      (Ext.mk₀ a) (add_zero 1)).hom = mapExtensionEndpoints F e z a := by
  simp only [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀,
    Ext.mapExactFunctor_hom, mapExtensionEndpoints, mapSingleArrow, ShiftedHom.map,
    Int.natCast_one, Category.assoc]

private theorem mapExtensionEndpoints_square
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    {E : Type u₃} [Category.{v₃} E] [Abelian E]
    {H : Type u₄} [Category.{v₄} H] [Abelian H]
    [HasDerivedCategory.{t₁} C] [HasDerivedCategory.{t₂} D]
    [HasDerivedCategory.{t₃} E] [HasDerivedCategory.{t₄} H]
    [HasExt.{w₁} C] [HasExt.{w₂} D] [HasExt.{w₃} E] [HasExt.{w₄} H]
    [EnoughInjectives C]
    (V : C ⥤ D) [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (P : D ⥤ H) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (Q : C ⥤ E) [Q.Additive] [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (W : E ⥤ H) [W.Additive] [PreservesFiniteLimits W] [PreservesFiniteColimits W]
    (κ : V ⋙ P ≅ Q ⋙ W) {A B : C} {A' B' : D} {A'' B'' : E} {A''' B''' : H}
    (e : Ext.{w₁} A B 1) (iY : A' ⟶ V.obj A) (bY : V.obj B ⟶ B')
    (z : P.obj A' ⟶ A''') (a : P.obj B' ⟶ B''')
    (iX : A''' ⟶ W.obj A'') (bX : W.obj B'' ⟶ B''')
    (zEt : A'' ⟶ Q.obj A) (bEt : Q.obj B ⟶ B'')
    (hz : P.map iY ≫ κ.hom.app A = z ≫ iX ≫ W.map zEt)
    (hu : κ.inv.app B ≫ P.map bY ≫ a = W.map bEt ≫ bX) :
    mapSingleArrow P 1 (mapExtensionEndpoints V e iY bY) ≫
        ((DerivedCategory.singleFunctor H 0).map a)⟦(1 : ℤ)⟧' =
      (DerivedCategory.singleFunctor H 0).map z ≫
        mapExtensionEndpoints W
          (((Ext.mk₀ zEt).comp (e.mapExactFunctor Q) (zero_add 1)).comp
            (Ext.mk₀ bEt) (add_zero 1)) iX bX := by
  let S := DerivedCategory.singleFunctor H 0
  have hcomp := mapSingleArrow_comp_iso V P (Q ⋙ W) κ.symm e
  have hcomp' := mapSingleArrow_comp_iso Q W (Q ⋙ W) (Iso.refl _) e
  simp only [Iso.refl_inv, Iso.refl_hom, NatTrans.id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] at hcomp'
  have hmap : mapSingleArrow P 1 (mapSingleArrow V 1 e.hom) =
      S.map (κ.hom.app _) ≫ mapSingleArrow W 1 (mapSingleArrow Q 1 e.hom) ≫
        (S.map (κ.inv.app _))⟦(1 : ℤ)⟧' := by
    rw [hcomp, ← hcomp']
    rfl
  simp only [mapExtensionEndpoints, mapExtensionEndpoints_hom]
  rw [mapSingleArrow_precomp, mapSingleArrow_postcomp, hmap,
    mapSingleArrow_precomp, mapSingleArrow_postcomp]
  simp only [Category.assoc]
  have hz' : S.map (P.map iY) ≫ S.map (κ.hom.app _) =
      S.map z ≫ S.map iX ≫ S.map (W.map zEt) := by
    simpa only [Functor.map_comp, Category.assoc] using congrArg S.map hz
  have hu' : (S.map (κ.inv.app B))⟦(1 : ℤ)⟧' ≫
      (S.map (P.map bY))⟦(1 : ℤ)⟧' ≫
      (S.map a)⟦(1 : ℤ)⟧' =
        (S.map (W.map bEt))⟦(1 : ℤ)⟧' ≫
          (S.map bX)⟦(1 : ℤ)⟧' := by
    simpa only [Functor.map_comp, Category.assoc] using
      congrArg (fun k ↦ (S.map k)⟦(1 : ℤ)⟧') hu
  change S.map (P.map iY) ≫ S.map (κ.hom.app _) ≫
    mapSingleArrow W 1 (mapSingleArrow Q 1 e.hom) ≫
    (S.map (κ.inv.app B))⟦(1 : ℤ)⟧' ≫
    (S.map (P.map bY))⟦(1 : ℤ)⟧' ≫ (S.map a)⟦(1 : ℤ)⟧' = _
  rw [hu']
  simpa only [Category.assoc] using
    congrArg (fun k ↦ k ≫ mapSingleArrow W 1 (mapSingleArrow Q 1 e.hom) ≫
      (S.map (W.map bEt))⟦(1 : ℤ)⟧' ≫
        (S.map bX)⟦(1 : ℤ)⟧') hz'

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Change of site preserves an arbitrary integral units cohomology class with its
specified integer and full-units endpoints.
Source: blueprint classes proof (2), exact transport of integral extension classes;
Stacks Tag 00WX for the adjunction square.
(blueprint: lem-sp-integral-cohomology-site-pullback).

Proof: use integral_site_pullback_endpoints for the two ordinary endpoint squares.
Exact-functor Ext compatibility identifies the two composites under the canonical
comparisonUpperStarCompUpperStarIso. Apply Ext.hom and naturality of the single
and shift comparisons; precomposition and shifted postcomposition commute with
this transport. The integer square rewrites the source factor and the units square
rewrites the target factor. Their composites are exactly gmCohomologyMap followed
by the comparison inverse image and its integer and units endpoint maps. -/
theorem integral_cohomology_site_pullback {X Y : Scheme.{u₁}} (f : X ⟶ Y)
    (e : Sheaf.H Y.gmSheaf 1)
    (a : (upperStar AddCommGrpCat.{u₁ + 1} f).obj (Scheme.proEtaleUnitsSheaf Y) ⟶
      Scheme.proEtaleUnitsSheaf X)
    (ha : ∀ (U : Y.ProEtᵒᵖ) (x : (Scheme.proEtaleUnitsSheaf Y).obj.obj U),
      (((upperStarLowerStarAdjunction AddCommGrpCat.{u₁ + 1} f).homEquiv _ _) a).hom.app
          U x = ULift.up (Additive.ofMul
          (Units.map (pullback.fst U.unop.hom f).appTop.hom.toMonoidHom x.down.toMul))) :
    mapSingleArrow (upperStar AddCommGrpCat.{u₁ + 1} f) 1
        (mapExtensionEndpoints (comparisonUpperStar AddCommGrpCat.{u₁ + 1} Y) e
          (integerComparison Y).inv (cartierUnitsComparison Y)) ≫
        ((DerivedCategory.singleFunctor (DiagonalAb X) 0).map a)⟦(1 : ℤ)⟧' =
      (DerivedCategory.singleFunctor (DiagonalAb X) 0).map
          (((upperStarLowerStarAdjunction AddCommGrpCat.{u₁ + 1} f).homEquiv _ _).symm
            (Scheme.proEtaleConstantDirectImageMap f AddCommGrpCat.{u₁ + 1}
              (AddCommGrpCat.of (ULift.{u₁ + 1} ℤ)))) ≫
        mapExtensionEndpoints (comparisonUpperStar AddCommGrpCat.{u₁ + 1} X)
          (Scheme.gmCohomologyMap f 1 e)
          (integerComparison X).inv (cartierUnitsComparison X) := by
  obtain ⟨hz, hu⟩ := integral_site_pullback_endpoints f a ha
  have hg : Scheme.gmCohomologyMap f 1 e =
      ((Ext.mk₀
        (((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u₁ + 1} f).symm.app
          (AddCommGrpCat.of (ULift.{u₁ + 1} ℤ))).hom)).comp
        (e.mapExactFunctor (Etale.upperStar AddCommGrpCat.{u₁ + 1} f)) (zero_add 1)).comp
        (Ext.mk₀ (Scheme.upperStarGmSheafToGmSheaf f)) (add_zero 1) := by
    rfl
  rw [hg]
  exact mapExtensionEndpoints_square
    (comparisonUpperStar AddCommGrpCat.{u₁ + 1} Y)
    (upperStar AddCommGrpCat.{u₁ + 1} f)
    (Etale.upperStar AddCommGrpCat.{u₁ + 1} f)
    (comparisonUpperStar AddCommGrpCat.{u₁ + 1} X)
    (comparisonUpperStarCompUpperStarIso AddCommGrpCat.{u₁ + 1} f)
    e (integerComparison Y).inv (cartierUnitsComparison Y)
    _ a (integerComparison X).inv (cartierUnitsComparison X)
    _ (Scheme.upperStarGmSheafToGmSheaf f) hz hu

end AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
