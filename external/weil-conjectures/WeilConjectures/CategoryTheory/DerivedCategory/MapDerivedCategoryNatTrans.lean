/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryHomologyNatIso

/-!
# Natural transformations between exact functors on derived categories

A natural transformation `τ : F ⟶ G` of exact functors between abelian categories induces a
natural transformation `Functor.mapDerivedCategoryNatTrans τ : D(F) ⟶ D(G)` of the functors
induced on derived categories, computed levelwise on complexes. It is compatible with the
commutation isomorphisms `Functor.mapDerivedCategoryHomologyFunctorIso` with the homology
functors (`Functor.mapDerivedCategoryHomologyFunctorIso_hom_app_naturality_natTrans`). In
particular its component at `K` is an isomorphism as soon as `τ` is an isomorphism at every
cohomology object `Hⁿ(K)` (`Functor.isIso_mapDerivedCategoryNatTrans_app`).
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  {F G : C ⥤ D} [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- A natural transformation `τ : F ⟶ G` of exact functors between abelian categories induces a
natural transformation `F.mapDerivedCategory ⟶ G.mapDerivedCategory`, compatibly with the
localization functors. -/
noncomputable def mapDerivedCategoryNatTrans (τ : F ⟶ G) :
    F.mapDerivedCategory ⟶ G.mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Q (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    F.mapDerivedCategory G.mapDerivedCategory
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)) DerivedCategory.Q)

/-- The natural transformation `Functor.mapDerivedCategoryNatTrans τ` on the image of a cochain
complex is the levelwise image of `τ`. -/
@[reassoc]
lemma mapDerivedCategoryNatTrans_fac (τ : F ⟶ G) (K : CochainComplex C ℤ) :
    (mapDerivedCategoryNatTrans τ).app (DerivedCategory.Q.obj K) ≫
        G.mapDerivedCategoryFactors.hom.app K =
      F.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app K) := by
  have hF : Localization.Lifting.iso DerivedCategory.Q
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      F.mapDerivedCategory = F.mapDerivedCategoryFactors := rfl
  have hG : Localization.Lifting.iso DerivedCategory.Q
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      G.mapDerivedCategory = G.mapDerivedCategoryFactors := rfl
  simp only [mapDerivedCategoryNatTrans, Localization.liftNatTrans_app, hF, hG, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id]
  rfl

/-- The commutation isomorphisms `Functor.mapDerivedCategoryHomologyFunctorIso` with the
homology functors are natural in the exact functor, with respect to the natural transformation
`Functor.mapDerivedCategoryNatTrans τ` induced by `τ : F ⟶ G`. -/
@[reassoc]
lemma mapDerivedCategoryHomologyFunctorIso_hom_app_naturality_natTrans (τ : F ⟶ G) (n : ℤ)
    (K : DerivedCategory C) :
    τ.app ((DerivedCategory.homologyFunctor C n).obj K) ≫
        (G.mapDerivedCategoryHomologyFunctorIso n).hom.app K =
      (F.mapDerivedCategoryHomologyFunctorIso n).hom.app K ≫
        (DerivedCategory.homologyFunctor D n).map ((mapDerivedCategoryNatTrans τ).app K) := by
  have h : Functor.whiskerLeft (DerivedCategory.homologyFunctor C n) τ ≫
      (G.mapDerivedCategoryHomologyFunctorIso n).hom =
      (F.mapDerivedCategoryHomologyFunctorIso n).hom ≫
        Functor.whiskerRight (mapDerivedCategoryNatTrans τ)
          (DerivedCategory.homologyFunctor D n) := by
    refine Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) (fun L => ?_)
    have hfac : (mapDerivedCategoryNatTrans τ).app (DerivedCategory.Q.obj L) =
        F.mapDerivedCategoryFactors.hom.app L ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app L) ≫
            G.mapDerivedCategoryFactors.inv.app L := by
      rw [← mapDerivedCategoryNatTrans_fac_assoc, Iso.hom_inv_id_app]
      exact (Category.comp_id _).symm
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      mapDerivedCategoryHomologyFunctorIso_hom_app_Q, hfac, Category.assoc, Functor.map_comp]
    have h₂ : (F.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) n).inv.app L ≫
        (HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) n).map
          ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app L) =
        τ.app ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n).obj L) ≫
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
      reassoc_of% h₂, ← τ.naturality_assoc]
  exact congr_app h K

/-- The component of `Functor.mapDerivedCategoryNatTrans τ` at `K` is an isomorphism if `τ` is
an isomorphism at every cohomology object `Hⁿ(K)`. -/
lemma isIso_mapDerivedCategoryNatTrans_app (τ : F ⟶ G) (K : DerivedCategory C)
    (h : ∀ n : ℤ, IsIso (τ.app ((DerivedCategory.homologyFunctor C n).obj K))) :
    IsIso ((mapDerivedCategoryNatTrans τ).app K) := by
  rw [DerivedCategory.isIso_iff]
  intro n
  have e : (DerivedCategory.homologyFunctor D n).map ((mapDerivedCategoryNatTrans τ).app K) =
      (F.mapDerivedCategoryHomologyFunctorIso n).inv.app K ≫
        τ.app ((DerivedCategory.homologyFunctor C n).obj K) ≫
          (G.mapDerivedCategoryHomologyFunctorIso n).hom.app K := by
    rw [mapDerivedCategoryHomologyFunctorIso_hom_app_naturality_natTrans,
      Iso.inv_hom_id_app_assoc]
  rw [e]
  infer_instance

end CategoryTheory.Functor
