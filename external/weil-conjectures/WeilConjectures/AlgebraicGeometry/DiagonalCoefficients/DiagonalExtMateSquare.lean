/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.Tactic.CategoryTheory.Reassoc

/-! # Ext squares from the two endpoints of a derived mate

Source: diagonal tower coefficient changes (1), naturality and the Ext/Hom identification.
(blueprint: lem-diagonal-ext-mate-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u v u' v'
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

private theorem mate_square
    {C D K : Type*} [Category C] [Category D] [Category K]
    (F : C ⥤ D) (G : C ⥤ K) (H : K ⥤ D) (τ : F ⟶ G ⋙ H)
    {S T : C} {X Y X'' Y'' : D} {X' Y' : K}
    (sR : F.obj S ≅ X) (sA : G.obj S ≅ X')
    (e : H.obj X' ≅ X'') (v : H.obj Y' ⟶ Y'')
    (tR : F.obj T ⟶ Y) (tA : G.obj T ⟶ Y')
    (β : S ⟶ T) (r : X ⟶ Y) (a : X' ⟶ Y')
    (η : X ⟶ X'') (θ : Y ⟶ Y'')
    (hs : τ.app S ≫ H.map sA.hom ≫ e.hom = sR.hom ≫ η)
    (ht : τ.app T ≫ H.map tA ≫ v = tR ≫ θ)
    (hr : sR.hom ≫ r = F.map β ≫ tR)
    (ha : sA.hom ≫ a = G.map β ≫ tA) :
    η ≫ e.inv ≫ H.map a ≫ v = r ≫ θ := by
  apply (cancel_epi sR.hom).mp
  rw [← reassoc_of% hs]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_assoc]
  rw [ha]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% τ.naturality β, ht]
  rw [← reassoc_of% hr]

private theorem ext_square_of_hom
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C] [HasExt C]
    {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory D] [HasExt D]
    (F : D ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {X Y : C} {X' Y' : D} (r : Ext X Y 2) (a : Ext X' Y' 2)
    (η : X ⟶ F.obj X') (θ : Y ⟶ F.obj Y')
    (h : (DerivedCategory.singleFunctor C 0).map η ≫
        (F.mapDerivedCategorySingleFunctor 0).inv.app X' ≫
        F.mapDerivedCategory.map a.hom ≫
        (F.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app _ ≫
        ((F.mapDerivedCategorySingleFunctor 0).hom.app Y')⟦(2 : ℤ)⟧' =
      r.hom ≫ ((DerivedCategory.singleFunctor C 0).map θ)⟦(2 : ℤ)⟧') :
    (Ext.mk₀ η).comp (a.mapExactFunctor F) (zero_add 2) =
      r.comp (Ext.mk₀ θ) (add_zero 2) := by
  apply Ext.ext
  simpa only [Ext.comp_hom, Ext.mk₀_hom, Ext.mapExactFunctor_hom,
    ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀, ShiftedHom.map, Nat.cast_ofNat,
    Category.assoc] using h

private theorem ext_mate_square
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C] [HasExt C]
    {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory D] [HasExt D]
    (H : D ⥤ C) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    {B : Type*} [Category B]
    (F : B ⥤ DerivedCategory C) (G : B ⥤ DerivedCategory D)
    (τ : F ⟶ G ⋙ H.mapDerivedCategory)
    {S T : B} {X Y : C} {X' Y' : D}
    (sR : F.obj S ≅ (DerivedCategory.singleFunctor C 0).obj X)
    (sA : G.obj S ≅ (DerivedCategory.singleFunctor D 0).obj X')
    (tR : F.obj T ⟶ ((DerivedCategory.singleFunctor C 0).obj Y)⟦(2 : ℤ)⟧)
    (tA : G.obj T ⟶ ((DerivedCategory.singleFunctor D 0).obj Y')⟦(2 : ℤ)⟧)
    (β : S ⟶ T) (r : Ext X Y 2) (a : Ext X' Y' 2)
    (η : X ⟶ H.obj X') (θ : Y ⟶ H.obj Y')
    (hs : τ.app S ≫ H.mapDerivedCategory.map sA.hom ≫
        (H.mapDerivedCategorySingleFunctor 0).hom.app X' =
      sR.hom ≫ (DerivedCategory.singleFunctor C 0).map η)
    (ht : τ.app T ≫ H.mapDerivedCategory.map tA ≫
        (H.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app _ ≫
        ((H.mapDerivedCategorySingleFunctor 0).hom.app Y')⟦(2 : ℤ)⟧' =
      tR ≫ ((DerivedCategory.singleFunctor C 0).map θ)⟦(2 : ℤ)⟧')
    (hr : sR.hom ≫ r.hom = F.map β ≫ tR)
    (ha : sA.hom ≫ a.hom = G.map β ≫ tA) :
    (Ext.mk₀ η).comp (a.mapExactFunctor H) (zero_add 2) =
      r.comp (Ext.mk₀ θ) (add_zero 2) := by
  exact ext_square_of_hom H r a η θ
    (mate_square F G H.mapDerivedCategory τ sR sA
      ((H.mapDerivedCategorySingleFunctor 0).app X')
      ((H.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app _ ≫
        ((H.mapDerivedCategorySingleFunctor 0).hom.app Y')⟦(2 : ℤ)⟧')
      tR tA β r.hom a.hom ((DerivedCategory.singleFunctor C 0).map η)
      (((DerivedCategory.singleFunctor C 0).map θ)⟦(2 : ℤ)⟧') hs ht hr ha)

/-- The source and target equations for a derived natural comparison imply the
corresponding Yoneda square. The comparison is supplied by its independent
normalized endpoint calculations.

Source: diagonal tower coefficient changes (1), naturality and Ext/Hom.
(blueprint: lem-diagonal-ext-mate-square).
Proof: choose the comparison given by the source calculation, use the target
calculation for that same comparison, and apply naturality to the supplied arrow.
Cancel its source isomorphism and use exact-functor single/shift comparisons to
identify the resulting equality with composition in Ext. -/
theorem finiteCoefficient_extSquare_of_endpoints
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C] [HasExt C]
    {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory D] [HasExt D]
    (H : D ⥤ C) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    {B : Type*} [Category B]
    (F : B ⥤ DerivedCategory C) (G : B ⥤ DerivedCategory D)
    {I : Type*} (τ : I → (F ⟶ G ⋙ H.mapDerivedCategory)) (P : I → Prop)
    {S T : B} {X Y : C} {X' Y' : D}
    (sR : F.obj S ≅ (DerivedCategory.singleFunctor C 0).obj X)
    (sA : G.obj S ≅ (DerivedCategory.singleFunctor D 0).obj X')
    (tR : F.obj T ⟶ ((DerivedCategory.singleFunctor C 0).obj Y)⟦(2 : ℤ)⟧)
    (tA : G.obj T ⟶ ((DerivedCategory.singleFunctor D 0).obj Y')⟦(2 : ℤ)⟧)
    (β : S ⟶ T) (r : Ext X Y 2) (a : Ext X' Y' 2)
    (η : X ⟶ H.obj X') (θ : Y ⟶ H.obj Y')
    (hs : ∃! i : I, P i ∧ (τ i).app S ≫ H.mapDerivedCategory.map sA.hom ≫
        (H.mapDerivedCategorySingleFunctor 0).hom.app X' =
      sR.hom ≫ (DerivedCategory.singleFunctor C 0).map η)
    (ht : ∀ i : I, P i → (τ i).app T ≫ H.mapDerivedCategory.map tA ≫
        (H.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app _ ≫
        ((H.mapDerivedCategorySingleFunctor 0).hom.app Y')⟦(2 : ℤ)⟧' =
      tR ≫ ((DerivedCategory.singleFunctor C 0).map θ)⟦(2 : ℤ)⟧')
    (hr : sR.hom ≫ r.hom = F.map β ≫ tR)
    (ha : sA.hom ≫ a.hom = G.map β ≫ tA) :
    (Ext.mk₀ η).comp (a.mapExactFunctor H) (zero_add 2) =
      r.comp (Ext.mk₀ θ) (add_zero 2) := by
  obtain ⟨i, ⟨hi, hsource⟩, _⟩ := hs
  exact ext_mate_square H F G (τ i) sR sA tR tA β r a η θ
    hsource (ht i hi) hr ha

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
