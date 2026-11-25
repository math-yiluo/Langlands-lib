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
import WeilConjectures.CategoryTheory.SmoothPurity.UniversalUnitShift
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
/-! # Composition of derived scalar units
(blueprint: lem-sp-scalar-ext-unit-composition). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe uA uB uC vA vB vC wA wB wC wE
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace CategoryTheory.Functor
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
variable {A : Type uA} {B : Type uB} {C : Type uC}
  [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B] [HasDerivedCategory.{wC} C]
  [HasExt.{wE} C]
  (U : A ⥤ B) (V : B ⥤ C) [U.Additive] [V.Additive]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  [PreservesFiniteLimits V] [PreservesFiniteColimits V]

/-- Let U:A→B and V:B→C be exact additive functors, e∈Ext^n(F,VG) a V-derived Ext unit
[def-sp-derived-scalar-ext-unit], and θ:G→UH an ordinary U-derived unit
[def-sp-exact-functor-derived-unit]. Then e composed with mk0(Vθ) is a degree-n derived Ext unit for
U⋙V.
Source: blueprint Cartier derived reduction and comparison paragraphs; Stacks 0152,
06YY and 0GLZ (blueprint: lem-sp-scalar-ext-unit-composition).
Proof: Shift the ordinary unit bijection for θ by n using universal-unit shift. Compose it with the
universal bijection for e. The exact derived functor composition isomorphism transfers the resulting
target Hom set to D(U⋙V). Naturality of single comparisons, shift commutation and the formula for
composition with mk0 identify the resulting unit with e composed with mk0(Vθ). -/
theorem derivedExtUnit_comp {F : C} {G : B} {H : A} (n : ℕ)
    (e : Ext.{wE} F (V.obj G) n) (θ : G ⟶ U.obj H)
    (hη : V.DerivedExtUnit F G n e) (hθ : U.DerivedUnit G H θ) :
    (U ⋙ V).DerivedExtUnit F H n
      (e.comp (Ext.mk₀ (V.map θ)) (add_zero n)) := by
  let sA := DerivedCategory.singleFunctor A 0
  let sB := DerivedCategory.singleFunctor B 0
  let sC := DerivedCategory.singleFunctor C 0
  let pθ := sB.map θ ≫ (U.mapDerivedCategorySingleFunctor 0).inv.app H
  have hθ' : ∀ K, Function.Bijective (fun f : sA.obj H ⟶ K ↦
      pθ ≫ U.mapDerivedCategory.map f) := by
    intro K
    simpa only [pθ, Category.assoc] using hθ K
  have hshift := universal_unit_shift U.mapDerivedCategory pθ hθ' (n : ℤ)
  unfold DerivedExtUnit
  intro K
  have hb := (hη (U.mapDerivedCategory.obj K)).comp (hshift K)
  let z := (mapDerivedCategoryCompIso U V).symm.app K
  have he (f : (sA.obj H)⟦(n : ℤ)⟧ ⟶ K) :
      e.hom ≫ ((V.mapDerivedCategorySingleFunctor 0).inv.app G)⟦(n : ℤ)⟧' ≫
        (V.mapDerivedCategory.commShiftIso (n : ℤ)).inv.app (sB.obj G) ≫
          V.mapDerivedCategory.map
            (pθ⟦(n : ℤ)⟧' ≫ (U.mapDerivedCategory.commShiftIso (n : ℤ)).inv.app
              (sA.obj H) ≫ U.mapDerivedCategory.map f) =
      ((e.comp (Ext.mk₀ (V.map θ)) (add_zero n)).hom ≫
        (((U ⋙ V).mapDerivedCategorySingleFunctor 0).inv.app H)⟦(n : ℤ)⟧' ≫
          ((U ⋙ V).mapDerivedCategory.commShiftIso (n : ℤ)).inv.app (sA.obj H) ≫
            (U ⋙ V).mapDerivedCategory.map f) ≫ z.hom := by
    have hc := derivedCompSingle U V H
    have hci : (V.mapDerivedCategorySingleFunctor 0).inv.app (U.obj H) ≫
        V.mapDerivedCategory.map ((U.mapDerivedCategorySingleFunctor 0).inv.app H) =
      ((U ⋙ V).mapDerivedCategorySingleFunctor 0).inv.app H ≫
        (mapDerivedCategoryCompIso U V).inv.app (sA.obj H) := by
      let a := (V.mapDerivedCategorySingleFunctor 0).app (U.obj H)
      let b := V.mapDerivedCategory.mapIso ((U.mapDerivedCategorySingleFunctor 0).app H)
      apply (cancel_mono (b.hom ≫ a.hom)).1
      change (a.inv ≫ b.inv) ≫ (b.hom ≫ a.hom) = _
      simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id]
      change 𝟙 _ = ((U ⋙ V).mapDerivedCategorySingleFunctor 0).inv.app H ≫
        ((mapDerivedCategoryCompIso U V).inv.app (sA.obj H) ≫
          V.mapDerivedCategory.map ((U.mapDerivedCategorySingleFunctor 0).hom.app H) ≫
            (V.mapDerivedCategorySingleFunctor 0).hom.app (U.obj H))
      rw [hc]
      exact (Iso.inv_hom_id_app _ _).symm
    simp only [pθ, Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.comp_mk₀,
      Functor.map_comp, Category.assoc]
    rw [← V.mapDerivedCategory.commShiftIso_inv_naturality_assoc]
    rw [← (shiftFunctor (DerivedCategory C) (n : ℤ)).map_comp_assoc]
    erw [← (V.mapDerivedCategorySingleFunctor 0).inv.naturality θ]
    rw [← V.mapDerivedCategory.commShiftIso_inv_naturality_assoc]
    simp only [Functor.map_comp, Category.assoc]
    rw [← (shiftFunctor (DerivedCategory C) (n : ℤ)).map_comp_assoc
      ((V.mapDerivedCategorySingleFunctor 0).inv.app (U.obj H))]
    rw [hci]
    simp only [Functor.map_comp, Functor.comp_map, Category.assoc]
    have hco : ((U.mapDerivedCategory ⋙ V.mapDerivedCategory).commShiftIso (n : ℤ)).inv.app
        (sA.obj H) =
      (V.mapDerivedCategory.commShiftIso (n : ℤ)).inv.app (U.mapDerivedCategory.obj (sA.obj H)) ≫
        V.mapDerivedCategory.map
          ((U.mapDerivedCategory.commShiftIso (n : ℤ)).inv.app (sA.obj H)) := by
      simp only [Functor.commShiftIso_comp_inv_app]
    erw [← reassoc_of% hco]
    rw [NatTrans.shift_app_assoc (mapDerivedCategoryCompIso U V).inv]
    simp only [Iso.hom_inv_id_app_assoc]
    erw [← (mapDerivedCategoryCompIso U V).inv.naturality f]
    rfl
  have hb' : Function.Bijective (fun f : (sA.obj H)⟦(n : ℤ)⟧ ⟶ K ↦
      ((e.comp (Ext.mk₀ (V.map θ)) (add_zero n)).hom ≫
        (((U ⋙ V).mapDerivedCategorySingleFunctor 0).inv.app H)⟦(n : ℤ)⟧' ≫
          ((U ⋙ V).mapDerivedCategory.commShiftIso (n : ℤ)).inv.app (sA.obj H) ≫
            (U ⋙ V).mapDerivedCategory.map f) ≫ z.hom) := by
    simp only [Function.comp_def] at hb
    convert hb using 1
    · rfl
    · funext f
      exact (he f).symm
  apply Function.Bijective.of_comp_left (f := fun f ↦ f ≫ z.hom) hb'
  intro f g hfg
  exact (cancel_mono z.hom).1 hfg
end CategoryTheory.Functor
