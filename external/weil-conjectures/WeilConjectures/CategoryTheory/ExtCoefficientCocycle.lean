/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-! # Exact functors and coefficient maps on individual Ext cocycles

Source: Stacks Project, Tag 06XR; Tag 01F8, equations 01F9 and 01FA.
(blueprint: lem-weil-pbc-ext-coefficient-cocycle).
-/

@[expose] public section

universe v w w'
open CategoryTheory CochainComplex HomComplex Limits Abelian

namespace CategoryTheory.InjectiveResolution

set_option backward.isDefEq.respectTransparency false in
/-- An exact functor and a coefficient map send a single Ext cocycle to its image.
Source: Stacks Project, Tag 06XR; Tag 01F8, equations 01F9 and 01FA; Tag 013P.
(blueprint: lem-weil-pbc-ext-coefficient-cocycle)

Proof. Express the class of a as the derived-category roof with denominator the
augmentation of R. Exactness of L preserves this invertible denominator. The supplied
homotopy identifies L of the augmentation followed by φ with the single-complex
comparison followed by v and the augmentation of R'. Precompose the roof with α and
postcompose with v. Cancel the invertible target augmentation. The numerator is now
α;L(a);φ, which is the roof representing the displayed target cocycle. Injectivity of
Ext.hom gives equality of Ext classes. The assumptions ha and ha' ensure both roofs
represent cocycles. This is only the calculation on one cocycle, before descent to
homology or evaluation on sections. In degree zero the same roof calculation applies;
zero cocycles, zero coefficients and zero objects give zero on both sides. -/
theorem ext_mapExactFunctor_coefficient_cocycle
    {C : Type w} {D : Type w'} [Category.{v} C] [Category.{v} D]
    [Abelian C] [Abelian D] [HasExt.{v} C] [HasExt.{v} D]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {A B : C} {A' B' : D} (α : A' ⟶ L.obj A)
    (R : InjectiveResolution B) (R' : InjectiveResolution B') (v : L.obj B ⟶ B')
    (φ : (L.mapHomologicalComplex (.up ℤ)).obj R.cochainComplex ⟶ R'.cochainComplex)
    (hφ : Nonempty (Homotopy
      ((L.mapHomologicalComplex (.up ℤ)).map R.ι' ≫ φ)
      ((HomologicalComplex.singleMapHomologicalComplex L (.up ℤ) 0).hom.app B ≫
        (singleFunctor D 0).map v ≫ R'.ι')))
    (q : ℕ) (a : A ⟶ R.cochainComplex.X (q : ℤ))
    (ha : a ≫ R.cochainComplex.d (q : ℤ) ((q : ℤ) + 1) = 0)
    (ha' : (α ≫ L.map a ≫ φ.f (q : ℤ)) ≫
      R'.cochainComplex.d (q : ℤ) ((q : ℤ) + 1) = 0) :
    ((Ext.mk₀ α).comp
      ((R.extEquivCohomologyClass.symm
        (.mk (Cocycle.fromSingleMk a (zero_add (q : ℤ)) _ rfl ha))).mapExactFunctor L)
      (zero_add q)).comp (Ext.mk₀ v) (add_zero q) =
    R'.extEquivCohomologyClass.symm
      (.mk (Cocycle.fromSingleMk (α ≫ L.map a ≫ φ.f (q : ℤ))
        (zero_add (q : ℤ)) _ rfl ha')) := by
  let := HasDerivedCategory.standard C
  let := HasDerivedCategory.standard D
  have hsource : (L.mapDerivedCategorySingleFunctor 0).inv.app A ≫
      L.mapDerivedCategoryFactors.hom.app ((singleFunctor C 0).obj A) =
      DerivedCategory.Q.map ((L.mapCochainComplexSingleFunctor 0).inv.app A) := by
    simpa only [singleFunctor] using!
      L.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app A
  have hden : L.mapDerivedCategoryFactors.inv.app R.cochainComplex ≫
      L.mapDerivedCategory.map (inv (DerivedCategory.Q.map R.ι')) ≫
      (L.mapDerivedCategorySingleFunctor 0).hom.app B ≫
      DerivedCategory.Q.map ((singleFunctor D 0).map v) =
      DerivedCategory.Q.map φ ≫ inv (DerivedCategory.Q.map R'.ι') := by
    rw [← cancel_epi (DerivedCategory.Q.map
      ((L.mapHomologicalComplex (.up ℤ)).map R.ι'))]
    erw [L.mapDerivedCategoryFactors.inv.naturality_assoc,
      ← L.mapDerivedCategory.map_comp_assoc, IsIso.hom_inv_id,
      L.mapDerivedCategory.map_id, Category.id_comp]
    have hh := DerivedCategory.Q_map_eq_of_homotopy D hφ.some
    simp only [Functor.map_comp] at hh
    rw [reassoc_of% hh, IsIso.hom_inv_id, Category.comp_id]
    simpa only [singleFunctor, Category.assoc] using! congrArg
      (fun z ↦ z ≫ DerivedCategory.Q.map ((singleFunctor D 0).map v))
      (L.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app B)
  have hnum : (singleFunctor D 0).map α ≫
      (L.mapCochainComplexSingleFunctor 0).inv.app A ≫
      ShiftedHom.map (Cocycle.equivHomShift.symm
        (Cocycle.fromSingleMk a (zero_add (q : ℤ)) _ rfl ha))
          (L.mapHomologicalComplex (.up ℤ)) ≫ φ⟦(q : ℤ)⟧' =
      Cocycle.equivHomShift.symm
        (Cocycle.fromSingleMk (α ≫ L.map a ≫ φ.f (q : ℤ))
          (zero_add (q : ℤ)) _ rfl ha') := by
    apply HomologicalComplex.from_single_hom_ext
    dsimp [ShiftedHom.map]
    simp only [singleFunctor, Functor.comp_obj,
      HomologicalComplex.single_map_f_self, HomologicalComplex.singleObjXSelf,
      HomologicalComplex.singleObjXIsoOfEq, eqToIso_refl, Iso.refl_hom, Iso.refl_inv,
      Category.id_comp, Functor.mapCochainComplexSingleFunctor,
      HomologicalComplex.singleMapHomologicalComplex, NatIso.ofComponents_inv_app,
      ↓reduceDIte, eqToHom_refl, Cocycle.equivHomShift_symm_apply,
      Cocycle.homOf_f, Cocycle.rightShift_coe,
      Cocycle.fromSingleMk_coe, zero_add, Cochain.rightShift_v, Cochain.fromSingleMk_v,
      shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq, eqToIso.inv, Functor.map_comp,
      Category.comp_id, Category.assoc, eqToHom_naturality]
    erw [Category.id_comp, eqToHom_map]
  ext
  simp only [Ext.comp_hom, Ext.mk₀_hom, Ext.mapExactFunctor_hom,
    extEquivCohomologyClass_symm_mk_hom]
  simp only [DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, ShiftedHom.mk₀_id_comp,
    ShiftedHom.map_comp, ShiftedHom.map_mk₀]
  simp only [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀, Category.assoc]
  rw [← ShiftedHom.comp_map,
    ← ShiftedHom.map_naturality_2 _ L.mapDerivedCategoryFactors]
  simp only [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀, Category.assoc]
  erw [reassoc_of% hsource]
  erw [Category.comp_id, Category.comp_id]
  have hden' : L.mapDerivedCategoryFactors.inv.app R.cochainComplex ≫
      L.mapDerivedCategory.map (inv (DerivedCategory.Q.map R.ι')) ≫
      (L.mapDerivedCategorySingleFunctor 0).hom.app B ≫
      (DerivedCategory.singleFunctor D 0).map v =
      DerivedCategory.Q.map φ ≫ inv (DerivedCategory.Q.map R'.ι') := hden
  erw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, hden', Functor.map_comp]
  rw [ShiftedHom.comp_map]
  have hnum' :
      (ShiftedHom.mk₀ 0 rfl ((singleFunctor D 0).map α ≫
        (L.mapCochainComplexSingleFunctor 0).inv.app A)).comp
        ((ShiftedHom.map (Cocycle.equivHomShift.symm
          (Cocycle.fromSingleMk a (zero_add (q : ℤ)) _ rfl ha))
            (L.mapHomologicalComplex (.up ℤ))).comp
              (ShiftedHom.mk₀ 0 rfl φ) (zero_add _)) (add_zero _) =
      Cocycle.equivHomShift.symm
        (Cocycle.fromSingleMk (α ≫ L.map a ≫ φ.f (q : ℤ))
          (zero_add (q : ℤ)) _ rfl ha') := by
    simpa only [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀, Category.assoc] using hnum
  have hn := congrArg (fun f ↦ ShiftedHom.map f DerivedCategory.Q) hnum'
  rw [ShiftedHom.map_comp, ShiftedHom.map_comp,
    ShiftedHom.map_mk₀, ShiftedHom.map_mk₀] at hn
  simp only [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀,
    Functor.map_comp, Category.assoc] at hn
  erw [reassoc_of% hn]


end CategoryTheory.InjectiveResolution
