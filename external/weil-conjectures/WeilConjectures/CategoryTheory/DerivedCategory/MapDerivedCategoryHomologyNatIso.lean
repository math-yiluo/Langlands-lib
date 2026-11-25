/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Naturality of the homology isomorphism of an exact functor

Given an isomorphism `e : F ≅ G` of exact functors between abelian categories, we show that
the commutation isomorphisms `Functor.mapDerivedCategoryHomologyFunctorIso` of `F` and `G`
with the homology functors of the derived categories are compatible with `e` and the induced
isomorphism `Functor.mapDerivedCategoryNatIso e`.

## Main results

- `CategoryTheory.Functor.mapHomologicalComplexHomologyIso_hom_app_naturality`: the analogous
  naturality statement for `Functor.mapHomologicalComplexHomologyIso` on homological complexes.
- `CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso_hom_app_naturality`.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Functor

section

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  [CategoryWithHomology C] [CategoryWithHomology D]
  {ι : Type*} (c : ComplexShape ι) (i : ι)

/-- The component of `Functor.mapHomologicalComplexHomologyIso` at a complex `K` is the
isomorphism `ShortComplex.mapHomologyIso` of the short complex `K.sc i`. -/
lemma mapHomologicalComplexHomologyIso_hom_app_eq (F : C ⥤ D) [F.Additive]
    [F.PreservesHomology] (K : HomologicalComplex C c) :
    (F.mapHomologicalComplexHomologyIso c i).hom.app K = ((K.sc i).mapHomologyIso F).hom := by
  simp only [mapHomologicalComplexHomologyIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
    associator_hom_app, associator_inv_app, HomologicalComplex.homologyFunctorIso,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, mapHomologicalComplexCompShortComplexFunctorIso,
    ShortComplex.homologyFunctorIso, NatIso.ofComponents_hom_app, Functor.map_id,
    Category.id_comp]
  exact (Category.id_comp _).trans ((Category.id_comp _).trans
    ((congrArg (fun g => _ ≫ g) (F.map_id _)).trans (Category.comp_id _)))

/-- The isomorphism `Functor.mapHomologicalComplexHomologyIso` is natural in the functor. -/
@[reassoc]
lemma mapHomologicalComplexHomologyIso_hom_app_naturality
    {F G : C ⥤ D} [F.Additive] [G.Additive] [F.PreservesHomology] [G.PreservesHomology]
    (τ : F ⟶ G) (K : HomologicalComplex C c) :
    (HomologicalComplex.homologyFunctor D c i).map ((NatTrans.mapHomologicalComplex τ c).app K) ≫
        (G.mapHomologicalComplexHomologyIso c i).hom.app K =
      (F.mapHomologicalComplexHomologyIso c i).hom.app K ≫
        τ.app ((HomologicalComplex.homologyFunctor C c i).obj K) := by
  rw [mapHomologicalComplexHomologyIso_hom_app_eq, mapHomologicalComplexHomologyIso_hom_app_eq]
  refine (congrArg (· ≫ _) (ShortComplex.homologyMap_mapNatTrans (K.sc i) τ)).trans ?_
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

end

section

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]

/-- The isomorphism `Functor.mapDerivedCategoryHomologyFunctorIso` is natural in the exact
functor: it is compatible with an isomorphism `e : F ≅ G` and the induced isomorphism
`Functor.mapDerivedCategoryNatIso e` of functors between derived categories. -/
@[reassoc]
lemma mapDerivedCategoryHomologyFunctorIso_hom_app_naturality {F G : C ⥤ D}
    [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) (n : ℤ)
    (K : DerivedCategory C) :
    e.hom.app ((DerivedCategory.homologyFunctor C n).obj K) ≫
        (G.mapDerivedCategoryHomologyFunctorIso n).hom.app K =
      (F.mapDerivedCategoryHomologyFunctorIso n).hom.app K ≫
        (DerivedCategory.homologyFunctor D n).map ((mapDerivedCategoryNatIso e).hom.app K) := by
  have h : whiskerLeft (DerivedCategory.homologyFunctor C n) e.hom ≫
      (G.mapDerivedCategoryHomologyFunctorIso n).hom =
      (F.mapDerivedCategoryHomologyFunctorIso n).hom ≫
        whiskerRight (mapDerivedCategoryNatIso e).hom (DerivedCategory.homologyFunctor D n) := by
    refine Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) (fun L => ?_)
    have hfac : (mapDerivedCategoryNatIso e).hom.app (DerivedCategory.Q.obj L) =
        F.mapDerivedCategoryFactors.hom.app L ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app L) ≫
            G.mapDerivedCategoryFactors.inv.app L := by
      rw [← mapDerivedCategoryNatIso_fac_assoc, Iso.hom_inv_id_app]
      exact (Category.comp_id _).symm
    simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
      mapDerivedCategoryHomologyFunctorIso_hom_app_Q, hfac, Category.assoc, Functor.map_comp]
    have h₂ : (F.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) n).inv.app L ≫
        (HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) n).map
          ((NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app L) =
        e.hom.app ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n).obj L) ≫
          (G.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) n).inv.app L := by
      rw [← cancel_mono ((G.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) n).hom.app L),
        Category.assoc, Category.assoc, Iso.inv_hom_id_app,
        mapHomologicalComplexHomologyIso_hom_app_naturality,
        Iso.inv_hom_id_app_assoc]
      exact (Category.comp_id _).symm
    rw [← Iso.app_inv F.mapDerivedCategoryFactors L,
      ← Iso.app_hom F.mapDerivedCategoryFactors L,
      Iso.inv_hom_id_map_assoc, ← Functor.comp_map DerivedCategory.Q,
      ← (DerivedCategory.homologyFunctorFactors D n).inv.naturality_assoc,
      reassoc_of% h₂, ← e.hom.naturality_assoc]
  exact congr_app h K

end

end CategoryTheory.Functor
