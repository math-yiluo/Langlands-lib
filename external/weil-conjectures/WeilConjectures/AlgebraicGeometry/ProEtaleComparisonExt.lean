/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v uC uD vC vD wC wD hC hD
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace CategoryTheory.Functor
private theorem mapExt_bijective_of_fullyFaithfulPlus
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasExt.{wC} C]
    [HasDerivedCategory.{hC} C]
    {D : Type uD} [Category.{vD} D] [Abelian D] [HasExt.{wD} D]
    [HasDerivedCategory.{hD} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (hF : Nonempty F.mapDerivedCategoryPlus.FullyFaithful) (X Y : C) (n : ℕ) :
    Function.Bijective (fun c : Ext.{wC} X Y n ↦ Ext.mapExactFunctor.{wC, wD} F c) := by
  let K : DerivedCategory.Plus C :=
    ⟨(DerivedCategory.singleFunctor C 0).obj X, 0, inferInstance⟩
  let M : DerivedCategory.Plus C :=
    ⟨((DerivedCategory.singleFunctor C 0).obj Y)⟦(n : ℤ)⟧, -(n : ℤ),
      DerivedCategory.TStructure.t.isGE_shift _ 0 (n : ℤ) (-(n : ℤ))⟩
  obtain ⟨hf⟩ := hF
  let hcomp := (hf.comp (ObjectProperty.fullyFaithfulι _)).ofIso
    F.mapDerivedCategoryPlusCompatibility
  have hm : Function.Bijective (fun f : (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj Y)⟦(n : ℤ)⟧ ↦ F.mapDerivedCategory.map f) := by
    have h0 := ((ObjectProperty.fullyFaithfulι
      ((DerivedCategory.TStructure.t (C := C)).plus)).homEquiv (X := K) (Y := M)).bijective
    apply (Function.Bijective.of_comp_iff _ h0).1
    exact (hcomp.homEquiv (X := K) (Y := M)).bijective
  let eX := (F.mapDerivedCategorySingleFunctor 0).app X
  let eY := (F.mapDerivedCategory.commShiftIso (n : ℤ)).app
      ((DerivedCategory.singleFunctor C 0).obj Y) ≪≫
    (shiftFunctor _ (n : ℤ)).mapIso ((F.mapDerivedCategorySingleFunctor 0).app Y)
  have hb := (Iso.homCongr eX eY).bijective.comp (hm.comp Ext.homEquiv.bijective)
  have he (c : Ext.{wC} X Y n) :
      (Ext.mapExactFunctor.{wC, wD} F c).hom =
        eX.inv ≫ F.mapDerivedCategory.map c.hom ≫ eY.hom := by
    rw [Ext.mapExactFunctor_hom]
    simp only [ShiftedHom.map, eX, eY, Iso.trans_hom, Iso.app_hom,
      Iso.app_inv, Functor.mapIso_hom, Category.assoc]
  have hh : Function.Bijective (fun c : Ext.{wC} X Y n ↦
      (Ext.mapExactFunctor.{wC, wD} F c).hom) := by
    simpa only [Function.comp_def, Iso.homCongr_apply, he] using hb
  exact (Function.Bijective.of_comp_iff' Ext.homEquiv.bijective _).mp hh
end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale
variable (A : Type v) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]

/-- For a scheme Z, a Grothendieck abelian coefficient category A in the stated size universes,
etale A-sheaves X,Y and n≥0, exact etale-to-pro-etale comparison induces a bijection
Ext^n(X,Y)→Ext^n(ν*X,ν*Y) [proposition-comparison-morphism-inverse-image,
def-weil-abstract-derived-category].
Source: blueprint Cartier derived reduction and comparison paragraphs; Stacks 0152,
06YY and 0GLZ (auxiliary; not a blueprint node).
Proof: The bounded-below derived comparison is fully faithful: discrete injectives are acyclic for
comparison direct image and the comparison adjunction unit is invertible. Its fully faithful map on
Hom groups is bijective. The exact-functor Ext realization in the bounded-below derived category
commutes with comparison, giving the displayed unbounded Ext map in the selected HasExt models. -/
theorem comparison_mapExt_bijective (Z : Scheme.{u})
    [HasExt.{u + 1} (Sheaf Z.smallEtaleTopology A)]
    [HasExt.{u + 1} (Sheaf (Scheme.ProEt.topology Z) A)]
    (X Y : Sheaf Z.smallEtaleTopology A) (n : ℕ) :
    Function.Bijective (fun c : Ext.{u + 1} X Y n ↦
      Ext.mapExactFunctor.{u + 1, u + 1} (comparisonUpperStar A Z) c) := by
  let adj := comparisonAdjunction A Z
  have hu := isIso_comparisonAdjunction_unit A Z
  have hunit : IsIso adj.derivedPlus.unit := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro K
    exact Adjunction.isIso_derivedPlus_unit_app_of_rightAcyclic adj
      (fun _ _ ↦ inferInstance)
      (fun I _ ↦ rightAcyclic_comparisonUpperStar_obj_of_injective A Z I) K
  exact Functor.mapExt_bijective_of_fullyFaithfulPlus (comparisonUpperStar A Z)
    ⟨Adjunction.fullyFaithfulLOfIsIsoUnit adj.derivedPlus⟩ X Y n

end AlgebraicGeometry.ProEtale
