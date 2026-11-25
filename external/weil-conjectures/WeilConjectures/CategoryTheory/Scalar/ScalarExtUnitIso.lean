/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.Derived.DerivedScalarExtUnit
import all WeilConjectures.AlgebraicGeometry.ResidueQuotientDerivedUnit
import all WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.ExactFunctorDerivedUnit
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Data.ZMod.Basic
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Reduction
import all WeilConjectures.Algebra.Homology.DivisibleReduction.DivisibleExtensionDerivedReductionSupplement
import all WeilConjectures.Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import all WeilConjectures.SixFunctors.BaseChange.DerivedForget
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
import all Mathlib.CategoryTheory.Abelian.ShortExact
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe uA uB vA vB wA wB wE
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace CategoryTheory.Functor
variable {A : Type uA} {B : Type uB}
  [Category.{vA} A] [Category.{vB} B] [Abelian A] [Abelian B]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B] [HasExt.{wE} B]
  (U V : A ⥤ B) [U.Additive] [V.Additive]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  [PreservesFiniteLimits V] [PreservesFiniteColimits V]
/-- For exact additive functors U,V:A→B and an isomorphism ε:U≅V, if e∈Ext^n(F,UH) is a derived Ext
unit [def-sp-derived-scalar-ext-unit], then e composed with mk0(ε_H) is a V-derived Ext unit.
Source: blueprint Cartier derived reduction and comparison paragraphs; Stacks 0152,
06YY and 0GLZ (blueprint: lem-sp-scalar-ext-unit-iso).
Proof: The derived natural isomorphism sends each target Hom set for U to the corresponding one for
V. Compose this bijection with the unit bijection for e. Naturality of the exact-functor single
comparison and the shift equation for the derived natural isomorphism identify the composed function
with the unit function of e composed with mk0(ε_H). -/
theorem derivedExtUnit_iso (ε : U ≅ V) (F : B) (H : A) (n : ℕ)
    (η : Ext.{wE} F (U.obj H) n) (h : U.DerivedExtUnit F H n η) :
    V.DerivedExtUnit F H n (η.comp (Ext.mk₀ (ε.hom.app H)) (add_zero n)) := by
  unfold DerivedExtUnit at *
  let e := mapDerivedCategoryNatIso ε
  have hn : (U.mapDerivedCategorySingleFunctor 0).inv.app H ≫
      e.hom.app ((DerivedCategory.singleFunctor A 0).obj H) =
    (DerivedCategory.singleFunctor B 0).map (ε.hom.app H) ≫
      (V.mapDerivedCategorySingleFunctor 0).inv.app H := by
    apply (cancel_mono ((V.mapDerivedCategorySingleFunctor 0).hom.app H)).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id]
    rw [derivedNatSingle U V ε H]
    simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  intro K
  have hb := (Iso.homCongr (Iso.refl _) (e.app K)).bijective.comp (h K)
  have he (f : ((DerivedCategory.singleFunctor A 0).obj H)⟦(n : ℤ)⟧ ⟶ K) :
      (η.hom ≫ ((U.mapDerivedCategorySingleFunctor 0).inv.app H)⟦(n : ℤ)⟧' ≫
        (U.mapDerivedCategory.commShiftIso (n : ℤ)).inv.app _ ≫
          U.mapDerivedCategory.map f) ≫ e.hom.app K =
      (η.comp (Ext.mk₀ (ε.hom.app H)) (add_zero n)).hom ≫
        ((V.mapDerivedCategorySingleFunctor 0).inv.app H)⟦(n : ℤ)⟧' ≫
          (V.mapDerivedCategory.commShiftIso (n : ℤ)).inv.app _ ≫
            V.mapDerivedCategory.map f := by
    simp only [Category.assoc, Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.comp_mk₀]
    rw [e.hom.naturality]
    rw [NatTrans.app_shift e.hom]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
    rw [← (shiftFunctor (DerivedCategory B) (n : ℤ)).map_comp_assoc, hn]
    simp only [Functor.map_comp, Category.assoc]
  simpa only [Function.comp_def, Iso.homCongr_apply, Iso.refl_inv,
    Category.id_comp, Iso.app_hom, he] using hb
end CategoryTheory.Functor
