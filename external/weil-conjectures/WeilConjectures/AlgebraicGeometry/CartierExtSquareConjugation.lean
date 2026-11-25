/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Supported.ProEtaleSupportedCoefficientReduction
public import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCycleClassDefsSupplement
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-! # Conjugation of a Cartier coefficient Ext square

Source: blueprint sec-six-functors-basics/sk-lem-geo-cartier/sk-lem-geo-cartier.proof.md,
coefficient extension and transport by comparison isomorphisms
(blueprint: lem-amb-cartier-ext-square-conjugation).

The statement concerns arbitrary sheaves and degree-two classes on the ordinary
pro-etale site. Its transported classes and coefficient maps are expanded explicitly.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Abelian

namespace AlgebraicGeometry.Etale

/-- A coefficient Ext square remains commutative after conjugating its four objects.
Source: blueprint sec-six-functors-basics/sk-lem-geo-cartier/sk-lem-geo-cartier.proof.md,
coefficient extension and transport by comparison isomorphisms
(blueprint: lem-amb-cartier-ext-square-conjugation).

Proof: write `[f]` for `Ext.mk₀ f` and let `F` be restriction of scalars. The
exact-functor Ext identities expand the left side, after which associativity and
`F.map (βa.inv ≫ βa.hom) = 𝟙` cancel the adjacent comparison maps. The result is
`[βb.hom] (([η₀] · F_*ga) · [F.map qa.hom])`. Expanding the right side cancels
`qb.hom ≫ qb.inv` and gives `[βb.hom] ((gb · [θ₀]) · [F.map qa.hom])`.
The assumed square identifies the middle factors. Only functoriality,
associativity, and inverse-isomorphism laws enter, so no Cartier or flatness
hypothesis is needed. -/
theorem cartier_ext_square_conjugation
    {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (T : Scheme.{u})
    {Fb Fb' Gb Gb' : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} R)}
    {Fa Fa' Ga Ga' : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} S)}
    (η₀ : Fb ⟶ (Sheaf.restrictScalars (Scheme.ProEt.topology T) φ).obj Fa)
    (θ₀ : Gb ⟶ (Sheaf.restrictScalars (Scheme.ProEt.topology T) φ).obj Ga)
    (gb : Ext Fb Gb 2) (ga : Ext Fa Ga 2)
    (h : (Ext.mk₀ η₀).comp
        (ga.mapExactFunctor (Sheaf.restrictScalars (Scheme.ProEt.topology T) φ))
        (zero_add 2) = gb.comp (Ext.mk₀ θ₀) (add_zero 2))
    (βb : Fb' ≅ Fb) (βa : Fa' ≅ Fa) (qb : Gb ≅ Gb') (qa : Ga ≅ Ga') :
    (Ext.mk₀ (βb.hom ≫ η₀ ≫
        (Sheaf.restrictScalars (Scheme.ProEt.topology T) φ).map βa.inv)).comp
      ((((Ext.mk₀ βa.hom).comp ga (zero_add 2)).comp (Ext.mk₀ qa.hom)
        (add_zero 2)).mapExactFunctor
          (Sheaf.restrictScalars (Scheme.ProEt.topology T) φ)) (zero_add 2) =
    (((Ext.mk₀ βb.hom).comp gb (zero_add 2)).comp (Ext.mk₀ qb.hom) (add_zero 2)).comp
      (Ext.mk₀ (qb.inv ≫ θ₀ ≫
        (Sheaf.restrictScalars (Scheme.ProEt.topology T) φ).map qa.hom)) (add_zero 2) := by
  let F := Sheaf.restrictScalars (Scheme.ProEt.topology T) φ
  have hη :
      (Ext.mk₀ (βb.hom ≫ η₀ ≫ F.map βa.inv)).comp
          ((((Ext.mk₀ βa.hom).comp ga (zero_add 2)).comp (Ext.mk₀ qa.hom)
            (add_zero 2)).mapExactFunctor F) (zero_add 2) =
        (Ext.mk₀ βb.hom).comp
          (((Ext.mk₀ η₀).comp (ga.mapExactFunctor F) (zero_add 2)).comp
            (Ext.mk₀ (F.map qa.hom)) (add_zero 2)) (zero_add 2) := by
    simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
      Ext.comp_assoc_of_third_deg_zero]
    rw [Ext.mk₀_comp_mk₀_assoc]
    simp only [Category.assoc]
    rw [← F.map_comp, βa.inv_hom_id, F.map_id]
    rw [← Ext.mk₀_comp_mk₀]
    rw [show η₀ ≫ 𝟙 (F.obj Fa) = η₀ from Category.comp_id _]
    simp only [Ext.comp_assoc_of_second_deg_zero]
  change
    (Ext.mk₀ (βb.hom ≫ η₀ ≫ F.map βa.inv)).comp
        ((((Ext.mk₀ βa.hom).comp ga (zero_add 2)).comp (Ext.mk₀ qa.hom)
          (add_zero 2)).mapExactFunctor F) (zero_add 2) =
      (((Ext.mk₀ βb.hom).comp gb (zero_add 2)).comp (Ext.mk₀ qb.hom) (add_zero 2)).comp
        (Ext.mk₀ (qb.inv ≫ θ₀ ≫ F.map qa.hom)) (add_zero 2)
  rw [hη, h]
  simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]
  simp

end AlgebraicGeometry.Etale
