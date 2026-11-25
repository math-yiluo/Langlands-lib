/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.EtaleExceptionalConstantTensor
public import WeilConjectures.SixFunctors.Etale.Derived.LeftDerivedUpperStarSingle
import WeilConjectures.CategoryTheory.Derived.DerivedSingleConstantsComparison

/-! # Pullback of the constant scalar coefficient -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local instance 2000] CategoryTheory.instAdditiveSheafConstantSheaf

attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.mapDerivedCategory Functor.rightDerivedFunctor
  derivedTensor upperStar lowerStar

/-- The derived constant inverse-image comparison on a single complex.
Source: Stacks Tag 07A6 (blueprint: lem-pur-etale-constant-pullback-single).
Proof: expand exact derivation, move its comparison through the constant single
isomorphism by naturality, apply derived single comparison, and cancel inverses. -/
theorem etaleConstantPullback_single
    (C : Type (u + 1)) [CommRing C] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : ModuleCat.{u + 1} C) :
    (upperStar (ModuleCat.{u + 1} C) f).leftDerivedFunctor.map
        (((constantSheaf Y.smallEtaleTopology
          (ModuleCat.{u + 1} C)).mapDerivedCategorySingleFunctor 0).inv.app M) ≫
      (exceptionalConstantPullbackIso C f).hom.app
        ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} C) 0).obj M) ≫
      ((constantSheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} C)).mapDerivedCategorySingleFunctor 0).hom.app M =
    (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} C) f).hom.app
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} C)).obj M) ≫
      (DerivedCategory.singleFunctor _ 0).map
        ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} C) f).hom.app M) := by
  have hc := Functor.derived_single_constants_comparison
    (constantSheaf Y.smallEtaleTopology ((ModuleCat.{u + 1} C)))
    (upperStar ((ModuleCat.{u + 1} C)) f)
    (constantSheaf X.smallEtaleTopology ((ModuleCat.{u + 1} C)))
    (Scheme.upperStarConstantSheafIso ((ModuleCat.{u + 1} C)) f) M
  simp only [exceptionalConstantPullbackIso, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Category.assoc]
  have hn := (leftDerivedUpperStarIsoMapDerivedCategory
    ((ModuleCat.{u + 1} C)) f).hom.naturality
      (((constantSheaf Y.smallEtaleTopology
        ((ModuleCat.{u + 1} C))).mapDerivedCategorySingleFunctor 0).inv.app M)
  rw [reassoc_of% hn]
  simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc] at hc
  rw [hc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [singleFunctorCompLeftDerivedUpperStarIso,
    Functor.singleFunctorCompLeftDerivedFunctorIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.assoc]
  rfl

end AlgebraicGeometry.Etale
