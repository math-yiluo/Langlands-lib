/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import WeilConjectures.AlgebraicGeometry.Cohomology.MayerVietorisExtFunctorSquare
/-! # Ext restriction along an exact functor

Source: Stacks Project, Section 01F7; functoriality of Ext.
-/
@[expose] public section
set_option autoImplicit false
universe w w' v v' u u'
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace CategoryTheory.Abelian.Ext
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]

/-- Apply an exact functor and identify its source and coefficient objects.
Source: Stacks Project, Section 01F7; functoriality of Ext.
(blueprint: lem-pc-ext-restriction-map-calculus) -/
noncomputable def restrictAddHom (J : C ⥤ D) [J.Additive]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    {A F : C} {B E : D} (e : J.obj A ≅ B) (d : J.obj F ≅ E) (n : ℕ) :
    Ext A F n →+ Ext B E n :=
  ((Ext.mk₀ d.hom).postcomp B (add_zero n)).comp
    (((Ext.mk₀ e.inv).precomp (J.obj F) (zero_add n)).comp (J.mapExtAddHom A F n))

/-- Restriction respects postcomposition when the coefficient square commutes.
Source: Stacks Project, Section 01F7; associativity and functoriality of Ext.
(blueprint: lem-pc-ext-restriction-map-calculus) -/
theorem restrictAddHom_comp (J : C ⥤ D) [J.Additive]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    {A F : C} {B E : D} (e : J.obj A ≅ B) (d : J.obj F ≅ E)
    (a : F ⟶ F) (b : E ⟶ E) (h : J.map a ≫ d.hom = d.hom ≫ b)
    (n : ℕ) (x : Ext A F n) :
    restrictAddHom J e d n (x.comp (Ext.mk₀ a) (add_zero n)) =
      (restrictAddHom J e d n x).comp (Ext.mk₀ b) (add_zero n) := by
  change ((Ext.mk₀ e.inv).comp
    ((x.comp (Ext.mk₀ a) (add_zero n)).mapExactFunctor J) (zero_add n)).comp
      (Ext.mk₀ d.hom) (add_zero n) =
    (((Ext.mk₀ e.inv).comp (x.mapExactFunctor J) (zero_add n)).comp
      (Ext.mk₀ d.hom) (add_zero n)).comp (Ext.mk₀ b) (add_zero n)
  simp only [mapExactFunctor_comp, mapExactFunctor_mk₀]
  simp only [comp_assoc_of_third_deg_zero, mk₀_comp_mk₀, h]

section Square
universe w₃ w₄ v₃ v₄ u₃ u₄
variable {C₃ : Type u₃} [Category.{v₃} C₃] [Abelian C₃] [HasExt.{w₃} C₃]
  {C₄ : Type u₄} [Category.{v₄} C₄] [Abelian C₄] [HasExt.{w₄} C₄]

/-- The constructed restriction maps commute across a coherent exact-functor square.
Source: Stacks Project, Section 01F7; naturality of derived functor maps.
(blueprint: lem-pc-ext-restriction-map-calculus) -/
theorem restrictAddHom_square
    (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (J : C ⥤ C₃) [J.Additive] [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    (J' : D ⥤ C₄) [J'.Additive] [PreservesFiniteLimits J'] [PreservesFiniteColimits J']
    (GW : C₃ ⥤ C₄) [GW.Additive] [PreservesFiniteLimits GW] [PreservesFiniteColimits GW]
    (c : G ⋙ J' ≅ J ⋙ GW) {A F : C} {B E : C₃} {N : D} {NW : C₄}
    (e : J.obj A ≅ B) (d : J.obj F ≅ E) (d' : J'.obj N ≅ NW)
    (φ : G.obj F ⟶ N) (φW : GW.obj E ⟶ NW)
    (h : J'.map φ ≫ d'.hom = (c.app F).hom ≫ GW.map d.hom ≫ φW)
    (n : ℕ) (x : Ext A F n) :
    restrictAddHom J' ((c.app A) ≪≫ GW.mapIso e) d' n
      ((x.mapExactFunctor G).comp (Ext.mk₀ φ) (add_zero n)) =
    ((restrictAddHom J e d n x).mapExactFunctor GW).comp (Ext.mk₀ φW) (add_zero n) := by
  change ((Ext.mk₀ (((c.app A) ≪≫ GW.mapIso e).inv)).comp
    (((x.mapExactFunctor G).comp (Ext.mk₀ φ) (add_zero n)).mapExactFunctor J')
      (zero_add n)).comp (Ext.mk₀ d'.hom) (add_zero n) =
    ((((Ext.mk₀ e.inv).comp (x.mapExactFunctor J) (zero_add n)).comp
      (Ext.mk₀ d.hom) (add_zero n)).mapExactFunctor GW).comp
        (Ext.mk₀ φW) (add_zero n)
  simp only [mapExactFunctor_comp, mapExactFunctor_mk₀,
    comp_assoc_of_third_deg_zero, mk₀_comp_mk₀, h]
  rw [← mk₀_comp_mk₀ (c.app F).hom (GW.map d.hom ≫ φW)]
  rw [← comp_assoc_of_third_deg_zero
    ((x.mapExactFunctor G).mapExactFunctor J') (Ext.mk₀ (c.app F).hom)]
  rw [mapExactFunctor_square G J J' GW c n x]
  rw [comp_assoc_of_third_deg_zero]
  rw [← comp_assoc_of_second_deg_zero, mk₀_comp_mk₀]
  simp [Iso.trans_inv, Category.assoc]

end Square
end CategoryTheory.Abelian.Ext
