/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Adjunction.Limits
/-! # Products of functors commuting with shifts

Source: Stacks Project, Tag 011G; preservation of products by equivalences.
(blueprint: lem-weil-product-comm-shift)
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.ProductShift

universe a b c d e
variable {C : Type a} {D : Type b} [Category.{c} C] [Category.{d} D]
  [HasShift C ℤ] [HasShift D ℤ] {I : Type e} [HasProductsOfShape I D]
  (F : I → C ⥤ D) [∀ i, (F i).CommShift ℤ]
noncomputable abbrev productFunctor : C ⥤ D where
  obj X := ∏ᶜ fun i ↦ (F i).obj X
  map f := Limits.Pi.map (fun i ↦ (F i).map f)
  map_id X := by apply Limits.Pi.hom_ext; intro i; simp
  map_comp f g := by apply Limits.Pi.hom_ext; intro i; simp
noncomputable def productShiftIso (X : C) (m : ℤ) :
    (productFunctor F).obj (X⟦m⟧) ≅ ((productFunctor F).obj X)⟦m⟧ :=
  Limits.Pi.mapIso (fun i ↦ ((F i).commShiftIso m).app X) ≪≫
    (PreservesProduct.iso (shiftFunctor D m) (fun i ↦ (F i).obj X)).symm
@[reassoc]
lemma productShiftIso_π (X : C) (m : ℤ) (i : I) :
    (productShiftIso F X m).hom ≫ (Limits.Pi.π (fun i ↦ (F i).obj X) i)⟦m⟧' =
      Limits.Pi.π (fun i ↦ (F i).obj (X⟦m⟧)) i ≫ ((F i).commShiftIso m).hom.app X := by
  change _ ≫ (shiftFunctor D m).map (Limits.Pi.π _ i) = _
  rw [← piComparison_comp_π (shiftFunctor D m) (fun i ↦ (F i).obj X) i]
  simp only [productShiftIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    ← PreservesProduct.iso_hom, Iso.inv_hom_id_assoc]
  simpa only [Iso.app_hom, Functor.comp_obj, productFunctor] using
    (Limits.Pi.mapIso_hom_π (fun i ↦ ((F i).commShiftIso m).app X) i)
omit [∀ i, (F i).CommShift ℤ] [HasShift C ℤ] in
lemma productShift_hom_ext (X : C) (m : ℤ) {T : D}
    {f g : T ⟶ ((productFunctor F).obj X)⟦m⟧}
    (h : ∀ i, f ≫ (Limits.Pi.π (fun i ↦ (F i).obj X) i)⟦m⟧' =
      g ≫ (Limits.Pi.π (fun i ↦ (F i).obj X) i)⟦m⟧') : f = g := by
  apply (cancel_mono (PreservesProduct.iso (shiftFunctor D m)
    (fun i ↦ (F i).obj X)).hom).mp
  apply Limits.Pi.hom_ext
  intro i
  simpa only [Category.assoc, PreservesProduct.iso_hom, piComparison_comp_π] using h i
omit [∀ i, (F i).CommShift ℤ] [HasShift C ℤ] [HasShift D ℤ] in
@[reassoc]
lemma productFunctor_map_π {X Y : C} (f : X ⟶ Y) (i : I) :
    (productFunctor F).map f ≫ Limits.Pi.π (fun i ↦ (F i).obj Y) i =
      Limits.Pi.π (fun i ↦ (F i).obj X) i ≫ (F i).map f := by
  exact Limits.Pi.map_π (fun i ↦ (F i).map f) i
lemma productShiftIso_naturality {X Y : C} (f : X ⟶ Y) (m : ℤ) :
    (productFunctor F).map (f⟦m⟧') ≫ (productShiftIso F Y m).hom =
      (productShiftIso F X m).hom ≫ ((productFunctor F).map f)⟦m⟧' := by
  apply productShift_hom_ext F Y m
  intro i
  simp only [Category.assoc, productShiftIso_π]
  rw [← Category.assoc, productFunctor_map_π]
  rw [Category.assoc, Functor.commShiftIso_hom_naturality]
  rw [← Functor.map_comp, productFunctor_map_π, Functor.map_comp]
  conv_rhs => rw [← Category.assoc, productShiftIso_π]
  simp only [Category.assoc]
noncomputable def productShiftNatIso (m : ℤ) :
    shiftFunctor C m ⋙ productFunctor F ≅ productFunctor F ⋙ shiftFunctor D m :=
  NatIso.ofComponents (fun X ↦ productShiftIso F X m)
    (fun f ↦ productShiftIso_naturality F f m)
lemma productShiftNatIso_zero :
    productShiftNatIso F 0 = Functor.CommShift.isoZero (productFunctor F) ℤ := by
  ext X
  apply productShift_hom_ext F X 0
  intro i
  change (productShiftIso F X 0).hom ≫ _ = _
  rw [productShiftIso_π, Functor.CommShift.isoZero_hom_app]
  rw [Category.assoc, ← (shiftFunctorZero D ℤ).inv.naturality]
  simp only [Functor.id_map]
  rw [← Category.assoc, productFunctor_map_π]
  rw [Category.assoc, (F i).commShiftIso_zero, Functor.CommShift.isoZero_hom_app]
lemma productShiftNatIso_add (m n : ℤ) : productShiftNatIso F (m + n) =
    Functor.CommShift.isoAdd (productShiftNatIso F m) (productShiftNatIso F n) := by
  ext X
  apply productShift_hom_ext F X (m + n)
  intro i
  change (productShiftIso F X (m + n)).hom ≫ _ = _
  rw [productShiftIso_π, Functor.CommShift.isoAdd_hom_app]
  simp only [productShiftNatIso, NatIso.ofComponents_hom_app]
  simp only [Category.assoc]
  rw [← (shiftFunctorAdd D m n).inv.naturality]
  simp only [Functor.comp_map]
  rw [← Functor.map_comp_assoc, productShiftIso_π, Functor.map_comp_assoc]
  rw [productShiftIso_π_assoc]
  have hp := productFunctor_map_π F ((shiftFunctorAdd C m n).hom.app X) i
  simp only [Functor.comp_obj] at hp
  rw [reassoc_of% hp]
  rw [(F i).commShiftIso_add, Functor.CommShift.isoAdd_hom_app]
@[instance_reducible]
noncomputable def productCommShift : (productFunctor F).CommShift ℤ where
  commShiftIso := productShiftNatIso F
  commShiftIso_zero := productShiftNatIso_zero F
  commShiftIso_add := productShiftNatIso_add F

end CategoryTheory.ProductShift
