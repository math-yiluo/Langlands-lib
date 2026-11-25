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

/-! # Transport of normalized scalar Ext units
(blueprint: lem-sp-derived-scalar-ext-unit-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe uA uB uC uD vA vB vC vD wA wB wC wD wEA wEB wEC wED
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
namespace CategoryTheory.Functor
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
variable {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD}
  [Category.{vA} A] [Category.{vB} B] [Category.{vC} C] [Category.{vD} D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
  [HasExt.{wEB} B] [HasExt.{wED} D]
  (E : C ⥤ A) (U : A ⥤ B) (T : B ⥤ D) (V : C ⥤ D)
  [E.IsEquivalence] [T.IsEquivalence]
  [E.Additive] [U.Additive] [T.Additive] [V.Additive]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  [PreservesFiniteLimits V] [PreservesFiniteColimits V]

/-- Let E:C≃A and T:B≃D be exact equivalences, U:A→B and V:C→D exact additive, and ρ:E⋙U⋙T≅V. If
a∈Ext^n(X,U(EH)) is a DerivedExtUnit [def-sp-derived-scalar-ext-unit], a source isomorphism c:TX≅F
and a class b∈Ext^n(F,VH) satisfy T(a)ρ_H=c b, then b is a V-derived Ext unit.
Source: blueprint Cartier derived reduction and comparison paragraphs; Stacks 0152,
06YY and 0GLZ (blueprint: lem-sp-derived-scalar-ext-unit-transport).
Proof: Transport the universal Hom bijections along the two derived equivalences and the derived
square isomorphism. Exact-functor single and shift coherence identifies the transported unit. The
assumed Ext equation identifies this unit with b, including its positive shift and the prescribed
source isomorphism. -/
theorem derivedExtUnit_transport (ρ₀ : E ⋙ U ⋙ T ≅ V)
    (X : B) (H : C) (F : D) (c : T.obj X ≅ F) (n : ℕ)
    (a : Ext.{wEB} X (U.obj (E.obj H)) n) (b : Ext.{wED} F (V.obj H) n)
    (hab : (a.mapExactFunctor T).comp (Ext.mk₀ (ρ₀.hom.app H)) (add_zero n) =
      (Ext.mk₀ c.hom).comp b (zero_add n))
    (h : U.DerivedExtUnit X (E.obj H) n a) : V.DerivedExtUnit F H n b := by
  let ρ : E.mapDerivedCategory ⋙ U.mapDerivedCategory ⋙ T.mapDerivedCategory ≅
      V.mapDerivedCategory :=
    isoWhiskerLeft E.mapDerivedCategory (mapDerivedCategoryCompIso U T) ≪≫
      (mapDerivedCategoryCompIso E (U ⋙ T)) ≪≫ mapDerivedCategoryNatIso ρ₀
  let sB := DerivedCategory.singleFunctor B 0
  let sA := DerivedCategory.singleFunctor A 0
  let sC := DerivedCategory.singleFunctor C 0
  let sD := DerivedCategory.singleFunctor D 0
  let eF : T.mapDerivedCategory.obj (sB.obj X) ≅ sD.obj F :=
    (T.mapDerivedCategorySingleFunctor 0).app X ≪≫ sD.mapIso c
  let eH : E.mapDerivedCategory.obj ((sC.obj H)⟦(n : ℤ)⟧) ≅
      (sA.obj (E.obj H))⟦(n : ℤ)⟧ :=
    (E.mapDerivedCategory.commShiftIso (n : ℤ)).app (sC.obj H) ≪≫
      (shiftFunctor (DerivedCategory A) (n : ℤ)).mapIso
        ((E.mapDerivedCategorySingleFunctor 0).app H)
  let p := a.hom ≫ ((U.mapDerivedCategorySingleFunctor 0).inv.app (E.obj H))⟦(n : ℤ)⟧' ≫
    (U.mapDerivedCategory.commShiftIso (n : ℤ)).inv.app (sA.obj (E.obj H))
  have ht := CategoryTheory.Sheaf.ConstantResidue.universal_transport
    U.mapDerivedCategory V.mapDerivedCategory E.mapDerivedCategory T.mapDerivedCategory
    ρ eF eH p (fun K ↦ by simpa only [p, Category.assoc] using h K)
  have hn : (eF.inv ≫ T.mapDerivedCategory.map (p ≫ U.mapDerivedCategory.map eH.inv) ≫
      ρ.hom.app ((sC.obj H)⟦(n : ℤ)⟧)) =
    b.hom ≫ ((V.mapDerivedCategorySingleFunctor 0).inv.app H)⟦(n : ℤ)⟧' ≫
      (V.mapDerivedCategory.commShiftIso (n : ℤ)).inv.app (sC.obj H) := by
    have : NatTrans.CommShift ρ.hom ℤ := by dsimp [ρ]; infer_instance
    have hr := derivedTripleNatSingle E U T V ρ₀ H
    have hri : T.mapDerivedCategory.map
        ((U.mapDerivedCategorySingleFunctor 0).inv.app (E.obj H) ≫
          U.mapDerivedCategory.map ((E.mapDerivedCategorySingleFunctor 0).inv.app H)) ≫
        ρ.hom.app (sC.obj H) =
      (T.mapDerivedCategorySingleFunctor 0).hom.app (U.obj (E.obj H)) ≫
        sD.map (ρ₀.hom.app H) ≫ (V.mapDerivedCategorySingleFunctor 0).inv.app H := by
      apply (cancel_mono ((V.mapDerivedCategorySingleFunctor 0).hom.app H)).1
      simp only [Category.assoc, Iso.inv_hom_id_app]
      rw [hr, ← T.mapDerivedCategory.map_comp_assoc]
      simp only [Category.assoc, ← U.mapDerivedCategory.map_comp_assoc,
        Iso.inv_hom_id_app]
      erw [U.mapDerivedCategory.map_id]
      simp only [Category.id_comp, Iso.inv_hom_id_app]
      erw [T.mapDerivedCategory.map_id, Category.id_comp, Category.comp_id]
    dsimp only [eF, eH, p, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv]
    rw [NatTrans.app_shift ρ.hom]
    simp only [Functor.map_comp, Category.assoc, Functor.commShiftIso_comp_hom_app]
    simp only [Functor.comp_map, ← U.mapDerivedCategory.map_comp_assoc,
      Iso.inv_hom_id_app, Functor.map_id, Category.id_comp,
      ← T.mapDerivedCategory.map_comp_assoc]
    rw [← U.mapDerivedCategory.commShiftIso_inv_naturality_assoc]
    simp only [Iso.inv_hom_id_app]
    erw [Category.comp_id]
    rw [← (shiftFunctor (DerivedCategory B) (n : ℤ)).map_comp]
    rw [T.mapDerivedCategory.map_comp]
    simp only [Category.assoc]
    rw [T.mapDerivedCategory.commShiftIso_hom_naturality_assoc]
    rw [← (shiftFunctor (DerivedCategory D) (n : ℤ)).map_comp_assoc, hri]
    simp only [Functor.map_comp, Category.assoc]
    have hh := congrArg (fun z : Ext.{wED} (T.obj X) (V.obj H) n ↦ z.hom) hab
    simp only [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.comp_mk₀,
      ShiftedHom.mk₀_comp] at hh
    simp only [Ext.mapExactFunctor_hom, ShiftedHom.map, Category.assoc] at hh
    have hh' := congrArg (fun z ↦ sD.map c.inv ≫ z ≫
      ((V.mapDerivedCategorySingleFunctor 0).inv.app H)⟦(n : ℤ)⟧' ≫
        (V.mapDerivedCategory.commShiftIso (n : ℤ)).inv.app (sC.obj H)) hh
    simpa only [sD, Category.assoc,
      ← (DerivedCategory.singleFunctor D 0).map_comp_assoc, Iso.inv_hom_id,
      Functor.map_id, Category.id_comp] using hh'
  unfold DerivedExtUnit
  intro K
  simpa only [hn, Category.assoc] using ht K
end CategoryTheory.Functor
