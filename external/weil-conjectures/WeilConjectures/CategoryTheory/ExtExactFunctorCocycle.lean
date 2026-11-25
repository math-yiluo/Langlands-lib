/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-! # Exact functors on cocycle representatives of Ext

Source: Stacks Project, Tag 06XR; Tag 01F8, equations 01F9 and 01FA.
-/

@[expose] public section

universe v w w'
open CategoryTheory CochainComplex HomComplex Limits Abelian

namespace CategoryTheory.InjectiveResolution

set_option backward.isDefEq.respectTransparency false in
/-- An exact functor sends the roof of a single cocycle to the roof of its image.
Source: Stacks Project, Tag 06XR; Tag 01F8, equations 01F9 and 01FA.
(blueprint: lem-weil-pbc-ext-exact-functor-cocycle)

Proof: Express the Ext class of the cocycle as the derived-category roof with
right arrow the augmentation, using extEquivCohomologyClass_symm_mk_hom.
The derived functor of L takes this roof to the roof of L(a), because L is
exact and hence preserves quasi-isomorphisms. Precomposition with α changes
the numerator to α;L(a). The augmentation homotopy becomes equality in the
homotopy category and then in the derived category. Thus the image of the
augmentation followed by φ equals the target augmentation, after the canonical
single-complex comparison. Cancel the invertible target augmentation to identify
the image roof with the roof of α;L(a);φ. Apply injectivity of Ext.hom.
This calculation only concerns cocycles; it does not assert a homology square
or construct the map on quotient groups. In degree zero the same roof calculation
holds, and if a or α is zero both roofs are zero. -/
theorem ext_mapExactFunctor_cocycle
    {C : Type w} {D : Type w'} [Category.{v} C] [Category.{v} D]
    [Abelian C] [Abelian D] [HasExt.{v} C] [HasExt.{v} D]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {A B : C} {A' : D} (α : A' ⟶ L.obj A)
    (R : InjectiveResolution B) (R' : InjectiveResolution (L.obj B))
    (φ : (L.mapHomologicalComplex (.up ℤ)).obj R.cochainComplex ⟶ R'.cochainComplex)
    (hφ : Nonempty (Homotopy
      ((L.mapHomologicalComplex (.up ℤ)).map R.ι' ≫ φ)
      ((HomologicalComplex.singleMapHomologicalComplex L (.up ℤ) 0).hom.app B ≫ R'.ι')))
    (q : ℕ) (a : A ⟶ R.cochainComplex.X (q : ℤ))
    (ha : a ≫ R.cochainComplex.d (q : ℤ) ((q : ℤ) + 1) = 0)
    (ha' : (α ≫ L.map a ≫ φ.f (q : ℤ)) ≫
      R'.cochainComplex.d (q : ℤ) ((q : ℤ) + 1) = 0) :
    (Ext.mk₀ α).comp
      ((R.extEquivCohomologyClass.symm
        (.mk (Cocycle.fromSingleMk a (zero_add (q : ℤ)) _ rfl ha))).mapExactFunctor L)
      (zero_add q) =
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
      (L.mapDerivedCategorySingleFunctor 0).hom.app B =
      DerivedCategory.Q.map φ ≫ inv (DerivedCategory.Q.map R'.ι') := by
    rw [← cancel_epi (DerivedCategory.Q.map
      ((L.mapHomologicalComplex (.up ℤ)).map R.ι'))]
    erw [L.mapDerivedCategoryFactors.inv.naturality_assoc,
      ← L.mapDerivedCategory.map_comp_assoc, IsIso.hom_inv_id,
      L.mapDerivedCategory.map_id, Category.id_comp]
    have hh := DerivedCategory.Q_map_eq_of_homotopy D hφ.some
    rw [Functor.map_comp, Functor.map_comp] at hh
    rw [reassoc_of% hh, IsIso.hom_inv_id, Category.comp_id]
    simpa only [singleFunctor] using!
      L.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app B
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
  erw [← Functor.map_comp, ← Functor.map_comp, hden, Functor.map_comp]
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
  have hn := congrArg (fun f => ShiftedHom.map f DerivedCategory.Q) hnum'
  rw [ShiftedHom.map_comp, ShiftedHom.map_comp,
    ShiftedHom.map_mk₀, ShiftedHom.map_mk₀] at hn
  simp only [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀,
    Functor.map_comp, Category.assoc] at hn
  erw [reassoc_of% hn]

end CategoryTheory.InjectiveResolution
