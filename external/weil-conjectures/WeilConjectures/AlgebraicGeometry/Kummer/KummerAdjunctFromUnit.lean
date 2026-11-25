/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctorExtension
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor

/-! # Scalar adjuncts from naturality of normalized evaluated units. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe w
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] CategoryTheory.Abelian.Ext DerivedCategory.singleFunctors
  DerivedCategory.singleFunctorIsoCompQ HasDerivedCategory.standard

/-- Naturality of the evaluated unit, with the two endpoint normalizations inserted. -/
private theorem evaluated_unit_ext_naturality
    {A B : Type*} [Category A] [Abelian A] [HasExt.{w} A]
    [Category B] [Abelian B] [HasExt.{w} B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    (T : DerivedCategory A ⥤ DerivedCategory B)
    (G : B ⥤ A) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (η : 𝟭 (DerivedCategory A) ⟶ T ⋙ G.mapDerivedCategory)
    {S M R : A} {X H : B}
    (a : T.obj ((DerivedCategory.singleFunctor A 0).obj S) ≅
      (DerivedCategory.singleFunctor B 0).obj X)
    (b : T.obj (((DerivedCategory.singleFunctor A 0).obj M)⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor B 0).obj H)⟦(2 : ℤ)⟧)
    (q : S ⟶ G.obj X) (t : G.obj H ⟶ R) (κ : Ext M R 1)
    (hq : η.app ((DerivedCategory.singleFunctor A 0).obj S) ≫
      G.mapDerivedCategory.map a.hom ≫ (G.mapDerivedCategorySingleFunctor 0).hom.app X =
      (DerivedCategory.singleFunctor A 0).map q)
    (hκ : η.app (((DerivedCategory.singleFunctor A 0).obj M)⟦(1 : ℤ)⟧) ≫
      G.mapDerivedCategory.map b.hom ≫
      (G.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app
        ((DerivedCategory.singleFunctor B 0).obj H) ≫
      ((G.mapDerivedCategorySingleFunctor 0).hom.app H)⟦(2 : ℤ)⟧' ≫
      ((DerivedCategory.singleFunctor A 0).map t)⟦(2 : ℤ)⟧' =
      -(κ.hom⟦(1 : ℤ)⟧' ≫
        (shiftFunctorAdd (DerivedCategory A) (1 : ℤ) 1).inv.app
          ((DerivedCategory.singleFunctor A 0).obj R)))
    (f : Ext S M 1) :
    (Ext.mk₀ q).comp
      (((Ext.homEquiv.symm (a.inv ≫ T.map f.hom ≫ b.hom)).mapExactFunctor G).comp
        (Ext.mk₀ t) (add_zero 2)) (zero_add 2) = -(f.comp κ rfl) := by
  apply Ext.ext
  simp only [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀,
    Ext.mapExactFunctor_hom, Equiv.apply_symm_apply, Ext.neg_hom]
  rw [← hq]
  simp only [ShiftedHom.map, Functor.map_comp, Category.assoc,
    Iso.hom_inv_id_app_assoc]
  rw [← G.mapDerivedCategory.map_comp_assoc a.hom a.inv, Iso.hom_inv_id,
    G.mapDerivedCategory.map_id, Category.id_comp]
  have hn := η.naturality f.hom
  simp only [Functor.id_map, Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  simpa only [ShiftedHom, Nat.cast_one, Nat.cast_ofNat, Preadditive.comp_neg, ShiftedHom.comp,
    shiftFunctorAdd',
    eqToIso_refl, Iso.refl_trans, Category.assoc] using!
      congrArg (fun z ↦ f.hom ≫ z) hκ

/-- Exact functoriality of Ext under composition, without an injective hypothesis. -/
private theorem ext_map_comp
    {A B C : Type*} [Category A] [Abelian A] [HasExt.{w} A]
    [Category B] [Abelian B] [HasExt.{w} B]
    [Category C] [Abelian C] [HasExt.{w} C]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : B ⥤ C) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {X Y : A} {n : ℕ} (e : Ext X Y n) :
    (e.mapExactFunctor F).mapExactFunctor G = e.mapExactFunctor (F ⋙ G) := by
  have h := Ext.mapExactFunctor_comp_mk₀_eq_sheaf F G (F ⋙ G) (Iso.refl _) e
  simpa only [Iso.refl_hom, NatTrans.id_app, Ext.comp_mk₀_id, Ext.mk₀_id_comp] using h.symm

/-- A supplied residue lift has the scalar adjunct prescribed by the two unit
normalizations. This is formal naturality and exact-functoriality of Ext. -/
theorem kummer_adjunct_from_unit
    {A B C J : Type*}
    [Category A] [Abelian A] [HasExt.{w} A]
    [Category B] [Abelian B] [HasExt.{w} B]
    [Category C] [Abelian C] [HasExt.{w} C]
    [Category J] [Abelian J] [HasExt.{w} J]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} J]
    (T : DerivedCategory A ⥤ DerivedCategory J)
    (E : J ⥤ B) [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (U : B ⥤ A) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (F : C ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (V : C ⥤ A) [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (σ : V ≅ F ⋙ U)
    (η : 𝟭 (DerivedCategory A) ⟶ T ⋙ (E ⋙ U).mapDerivedCategory)
    {S M : A} {X H : J} {Q P : C}
    (a : T.obj ((DerivedCategory.singleFunctor A 0).obj S) ≅
      (DerivedCategory.singleFunctor J 0).obj X)
    (b : T.obj (((DerivedCategory.singleFunctor A 0).obj M)⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor J 0).obj H)⟦(2 : ℤ)⟧)
    (s : E.obj X ≅ F.obj Q) (t : E.obj H ≅ F.obj P)
    (q : S ⟶ U.obj (E.obj X)) (g : S ⟶ V.obj Q) (κ : Ext M (V.obj P) 1)
    (hq : η.app ((DerivedCategory.singleFunctor A 0).obj S) ≫
      (E ⋙ U).mapDerivedCategory.map a.hom ≫
      ((E ⋙ U).mapDerivedCategorySingleFunctor 0).hom.app X =
      (DerivedCategory.singleFunctor A 0).map q)
    (hκ : η.app (((DerivedCategory.singleFunctor A 0).obj M)⟦(1 : ℤ)⟧) ≫
      (E ⋙ U).mapDerivedCategory.map b.hom ≫
      ((E ⋙ U).mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app
        ((DerivedCategory.singleFunctor J 0).obj H) ≫
      (((E ⋙ U).mapDerivedCategorySingleFunctor 0).hom.app H)⟦(2 : ℤ)⟧' ≫
      ((DerivedCategory.singleFunctor A 0).map (U.map t.hom ≫ σ.inv.app P))⟦(2 : ℤ)⟧' =
      -(κ.hom⟦(1 : ℤ)⟧' ≫ (shiftFunctorAdd (DerivedCategory A) (1 : ℤ) 1).inv.app
        ((DerivedCategory.singleFunctor A 0).obj (V.obj P))))
    (hg : q ≫ U.map s.hom ≫ σ.inv.app Q = g)
    (f : Ext S M 1) (e : Ext Q P 2)
    (he : e.mapExactFunctor F = (Ext.mk₀ s.inv).comp
      (((Ext.homEquiv.symm (a.inv ≫ T.map f.hom ≫ b.hom)).mapExactFunctor E).comp
        (Ext.mk₀ t.hom) (add_zero 2)) (zero_add 2)) :
    (Ext.mk₀ g).comp (e.mapExactFunctor V) (zero_add 2) = -(f.comp κ rfl) := by
  let c : Ext X H 2 := Ext.homEquiv.symm (a.inv ≫ T.map f.hom ≫ b.hom)
  have hn := evaluated_unit_ext_naturality T (E ⋙ U) η a b q
    (U.map t.hom ≫ σ.inv.app P) κ hq hκ f
  have he' := congrArg (Ext.mapExactFunctor U) he
  change (e.mapExactFunctor F).mapExactFunctor U =
    ((Ext.mk₀ s.inv).comp ((c.mapExactFunctor E).comp
      (Ext.mk₀ t.hom) (add_zero 2)) (zero_add 2)).mapExactFunctor U at he'
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀, Ext.mapExactFunctor_mk₀, ext_map_comp E U] at he'
  have hmap := Ext.mapExactFunctor_comp_mk₀_eq_sheaf F U V σ e
  rw [he'] at hmap
  have h := congrArg (fun z ↦ (Ext.mk₀ g).comp
    (z.comp (Ext.mk₀ (σ.inv.app P)) (add_zero 2)) (zero_add 2)) hmap
  have hsrc : g ≫ σ.hom.app Q ≫ U.map s.inv = q := by
    rw [← hg]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← U.map_comp,
      Iso.hom_inv_id, U.map_id, Category.comp_id]
  simp only [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
    Iso.hom_inv_id_app, Ext.comp_mk₀_id] at h
  simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀_assoc] at h
  rw [hsrc] at h
  exact h.trans (by
    simpa only [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀] using hn)

end AlgebraicGeometry.ProEtale
