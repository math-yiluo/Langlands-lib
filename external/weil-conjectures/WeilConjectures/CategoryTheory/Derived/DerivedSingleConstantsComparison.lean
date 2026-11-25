/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Compatibility of an exact composite comparison with single complexes

Source: Stacks Project, Tag 07A6, and localization functoriality.
-/

@[expose] public section

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
/-- Exact derived composition agrees with the two single comparisons.
Source: Mathlib `mapDerivedCategoryCompIso_fac` and naturality of
`mapDerivedCategoryFactors`; the final complex equality is checked in degree zero.
(blueprint: lem-kun-derived-single-constants-comparison). -/
private theorem single_comp {C D E : Type*} [Category C] [Category D] [Category E]
    [CategoryTheory.Abelian C] [CategoryTheory.Abelian D] [CategoryTheory.Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) (H : D ⥤ E) [F.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] (X : C) :
    (Functor.mapDerivedCategoryCompIso F H).inv.app
        ((DerivedCategory.singleFunctor C 0).obj X) ≫
      H.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).hom.app X) ≫
      (H.mapDerivedCategorySingleFunctor 0).hom.app (F.obj X) =
    ((F ⋙ H).mapDerivedCategorySingleFunctor 0).hom.app X := by
  rw [← Functor.mapDerivedCategoryCompIso_hom_app_comp_mapDerivedCategorySingleFunctor_hom_app,
    Iso.inv_hom_id_app_assoc]

/-- A derived natural isomorphism agrees with its coefficient map on a single object.
Source: `mapDerivedCategoryNatIso_fac` and the definition of
`mapDerivedCategorySingleFunctor`; check the resulting complex map in degree zero.
(blueprint: lem-kun-derived-single-constants-comparison). -/
private theorem single_nat {C D : Type*} [Category C] [Category D]
    [CategoryTheory.Abelian C] [CategoryTheory.Abelian D] [HasDerivedCategory C]
    [HasDerivedCategory D]
    (F H : C ⥤ D) [F.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] (e : F ≅ H) (X : C) :
    (Functor.mapDerivedCategoryNatIso e).hom.app
        ((DerivedCategory.singleFunctor C 0).obj X) ≫
      (H.mapDerivedCategorySingleFunctor 0).hom.app X =
    (F.mapDerivedCategorySingleFunctor 0).hom.app X ≫
      (DerivedCategory.singleFunctor D 0).map (e.hom.app X) := by
  simp only [Functor.mapDerivedCategorySingleFunctor, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  dsimp [DerivedCategory.singleFunctorIsoCompQ]
  simp only [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp, Category.assoc]
  erw [Functor.mapDerivedCategoryNatIso_fac_assoc]
  change F.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor C 0).obj X) ≫
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app
          ((CochainComplex.singleFunctor C 0).obj X)) ≫
      DerivedCategory.Q.map ((H.mapCochainComplexSingleFunctor 0).hom.app X) =
    F.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor C 0).obj X) ≫
      DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).hom.app X) ≫
      DerivedCategory.Q.map ((CochainComplex.singleFunctor D 0).map (e.hom.app X))
  congr 1
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  apply HomologicalComplex.to_single_hom_ext
  simp only [Functor.comp_obj, HomologicalComplex.comp_f,
    NatTrans.mapHomologicalComplex_app_f]
  change e.hom.app X ≫
      ((HomologicalComplex.singleMapHomologicalComplex H (.up ℤ) 0).hom.app X).f 0 =
    ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app X).f 0 ≫
      ((HomologicalComplex.single D (.up ℤ) 0).map (e.hom.app X)).f 0
  simp only [HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    HomologicalComplex.single_map_f_self]
  dsimp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  erw [Category.id_comp]

/-- A descended comparison between a composite and another exact functor has its
ordinary value on single complexes. Source: Stacks Project, Tag 07A6.
(blueprint: lem-kun-derived-single-constants-comparison).

Proof: the localization factorization gives compatibility of exact composition
with the single comparisons. Naturality gives compatibility for an ordinary
natural isomorphism, as can be checked in degree zero. Compose these two identities
and cancel the inverse composition comparison. -/
theorem derived_single_constants_comparison
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) (H : D ⥤ E) (K : C ⥤ E)
    [F.Additive] [H.Additive] [K.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    (e : F ⋙ H ≅ K) (X : C) :
    (Functor.mapDerivedCategoryCompIso F H ≪≫
        Functor.mapDerivedCategoryNatIso e).hom.app
          ((DerivedCategory.singleFunctor C 0).obj X) ≫
      (K.mapDerivedCategorySingleFunctor 0).hom.app X =
    H.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).hom.app X) ≫
      (H.mapDerivedCategorySingleFunctor 0).hom.app (F.obj X) ≫
      (DerivedCategory.singleFunctor E 0).map (e.hom.app X) := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  rw [single_nat, ← single_comp F H]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]

end CategoryTheory.Functor
