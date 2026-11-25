/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFlat
public import WeilConjectures.EtaleCohomology.Purity.Smooth.ReductionKummerDelta

/-!
# The unit of the derived adjunction with an exact right adjoint

Let `adj : f ⊣ g` be an adjunction of additive functors between abelian categories, with `f`
left derivable through K-flat resolutions and `g` exact, and
`L(f) ⊣ g.mapDerivedCategory` the derived adjunction, with the right adjoint identified with
the levelwise functor (`Functor.rightDerivedFunctorIsoMapDerivedCategory`). On the image of a
complex `K` of the homotopy category, the unit of this adjunction followed by the counit of
`L(f)` is the levelwise unit of `adj`
(`CategoryTheory.Adjunction.derivedAdjunctionMapDerivedCategory_unit_app_fac`).
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory Abelian

namespace CategoryTheory

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [HasKInjectiveResolutions D]
  {f : C ⥤ D} {g : D ⥤ C} [f.Additive] [g.Additive] [f.PreservesKFlatQuasiIso]
  [PreservesFiniteLimits g] [PreservesFiniteColimits g]

/-- The derived adjunction `L(f) ⊣ g.mapDerivedCategory` of an adjunction `f ⊣ g` with `g`
exact. -/
noncomputable def Adjunction.derivedAdjunctionMapDerivedCategory (adj : f ⊣ g) :
    f.leftDerivedFunctor ⊣ g.mapDerivedCategory :=
  adj.derivedAdjunction.ofNatIsoRight g.rightDerivedFunctorIsoMapDerivedCategory

/-- The unit of `L(f) ⊣ g.mapDerivedCategory` on the image of a complex `K`, followed by the
counit `L(f)(K) ⟶ f(K)` and the factorization of `g.mapDerivedCategory`, is the levelwise unit
of `adj`. -/
theorem Adjunction.derivedAdjunctionMapDerivedCategory_unit_app_fac (adj : f ⊣ g)
    (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    adj.derivedAdjunctionMapDerivedCategory.unit.app (DerivedCategory.Qh.obj K) ≫
        g.mapDerivedCategory.map (f.leftDerivedFunctorCounit.app K) ≫
        g.mapDerivedCategoryFactorsh.hom.app ((f.mapHomotopyCategory _).obj K) =
      DerivedCategory.Qh.map ((adj.mapHomotopyCategory (ComplexShape.up ℤ)).unit.app K) := by
  have h₁ := adj.mapHomotopyCategory (ComplexShape.up ℤ) |>.derivedη_fac_app
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) f.leftDerivedFunctorCounit
    g.rightDerivedFunctorUnit K
  have h₃ := NatTrans.congr_app g.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
    ((f.mapHomotopyCategory _).obj K)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h₃
  have h₄ := g.rightDerivedFunctorIsoMapDerivedCategory.hom.naturality
    (f.leftDerivedFunctorCounit.app K)
  simp only [Adjunction.derivedAdjunctionMapDerivedCategory, Adjunction.derivedAdjunction,
    Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Category.assoc]
  erw [← reassoc_of% h₄, reassoc_of% h₁]
  rw [reassoc_of% h₃, Iso.inv_hom_id_app]
  exact Category.comp_id _

set_option linter.flexible false in
/-- The unit of `L(f) ⊣ g.mapDerivedCategory` on a flat object `P` placed in degree zero,
followed by `L(f)(P[0]) ≅ (f P)[0]` (`Functor.leftDerivedFunctorSingleFunctorIsoOfFlat`), is
the unit `P ⟶ g (f P)` of `adj` placed in degree zero. -/
theorem Adjunction.derivedAdjunctionMapDerivedCategory_unit_app_singleFunctor (adj : f ⊣ g)
    {P : C} (hP : ObjectProperty.flat P) :
    adj.derivedAdjunctionMapDerivedCategory.unit.app ((DerivedCategory.singleFunctor C 0).obj P) ≫
        g.mapDerivedCategory.map (f.leftDerivedFunctorSingleFunctorIsoOfFlat hP).hom =
      (DerivedCategory.singleFunctor C 0).map (adj.unit.app P) ≫
        (g.mapDerivedCategorySingleFunctor 0).inv.app (f.obj P) := by
  have hU := adj.derivedAdjunctionMapDerivedCategory_unit_app_fac
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
      ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj P))
  rw [mapHomotopyCategory_unit_app_quotient] at hU
  have hU' : adj.derivedAdjunctionMapDerivedCategory.unit.app (DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj P))) ≫
      g.mapDerivedCategory.map (f.leftDerivedFunctorCounit.app
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj P))) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app
          ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj P))) ≫
        g.mapDerivedCategoryFactorsh.inv.app ((f.mapHomotopyCategory _).obj
          ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
            ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj P))) := by
    rw [← hU]
    simp
  simp only [Functor.leftDerivedFunctorSingleFunctorIsoOfFlat, Iso.trans_hom, Functor.mapIso_hom,
    asIso_hom, Iso.app_hom, Iso.symm_hom, Functor.map_comp,
    Category.assoc]
  erw [adj.derivedAdjunctionMapDerivedCategory.unit_naturality_assoc,
    adj.derivedAdjunctionMapDerivedCategory.unit_naturality_assoc]
  erw [reassoc_of% hU']
  have hinv : g.mapDerivedCategoryFactorsh.inv.app
      ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj
        ((f.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj P))) =
      DerivedCategory.Qh.map ((g.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app _) ≫
        (DerivedCategory.quotientCompQhIso C).hom.app _ ≫
        g.mapDerivedCategoryFactors.inv.app _ ≫
        g.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso D).inv.app _) := by
    rw [← cancel_epi (g.mapDerivedCategoryFactorsh.hom.app _), Iso.hom_inv_id_app,
      g.mapDerivedCategoryFactorsh_hom_app]
    simp [← Functor.map_comp]
  erw [hinv]
  simp [Functor.mapHomotopyCategoryFactors, Functor.mapDerivedCategorySingleFunctor]
  have hc : (adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app
        ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj P) ≫
      (g.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex f (ComplexShape.up ℤ) 0).hom.app P) =
      (HomologicalComplex.single C (ComplexShape.up ℤ) 0).map (adj.unit.app P) ≫
        (HomologicalComplex.singleMapHomologicalComplex g (ComplexShape.up ℤ) 0).inv.app
          (f.obj P) := by
    apply HomologicalComplex.from_single_hom_ext
    simp [HomologicalComplex.single_map_f_self]
  have hq := (DerivedCategory.quotientCompQhIso C).hom.naturality
    ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app
      ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj P))
  have hn := g.mapDerivedCategoryFactors.inv.naturality
    ((HomologicalComplex.singleMapHomologicalComplex f (ComplexShape.up ℤ) 0).hom.app P)
  simp only [Functor.comp_map] at hq hn
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  erw [reassoc_of% hq, Iso.inv_hom_id_app_assoc]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, ← reassoc_of% hn, ← DerivedCategory.Q.map_comp_assoc, hc]
  rw [Functor.map_comp_assoc]


/-- The transpose under `L(f) ⊣ g.mapDerivedCategory` of a morphism `P ⟶ g P'` placed in degree
zero, `P` flat, is `L(f)(P[0]) ≅ (f P)[0]` followed by its transpose `f P ⟶ P'` under `f ⊣ g`
placed in degree zero. -/
theorem Adjunction.singleTranspose_derivedAdjunctionMapDerivedCategory (adj : f ⊣ g)
    {P : C} (hP : ObjectProperty.flat P) {P' : D} (φ : P ⟶ g.obj P') :
    ShortComplex.ShortExact.singleTranspose g adj.derivedAdjunctionMapDerivedCategory φ =
      (f.leftDerivedFunctorSingleFunctorIsoOfFlat hP).hom ≫
        (DerivedCategory.singleFunctor D 0).map ((adj.homEquiv _ _).symm φ) := by
  apply (adj.derivedAdjunctionMapDerivedCategory.homEquiv _ _).injective
  have hm := (g.mapDerivedCategorySingleFunctor 0).inv.naturality ((adj.homEquiv _ _).symm φ)
  simp only [Functor.comp_map] at hm
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    ShortComplex.ShortExact.unit_app_comp_map_singleTranspose, Functor.map_comp,
    reassoc_of% adj.derivedAdjunctionMapDerivedCategory_unit_app_singleFunctor hP, ← hm,
    ← Functor.map_comp_assoc, ← Adjunction.homEquiv_unit, Equiv.apply_symm_apply]

/-- The transpose under `L(f) ⊣ g.mapDerivedCategory` of a morphism `P ⟶ g P'` placed in degree
zero, `P` flat, is an isomorphism if its transpose `f P ⟶ P'` under `f ⊣ g` is. -/
lemma Adjunction.isIso_singleTranspose_derivedAdjunctionMapDerivedCategory (adj : f ⊣ g)
    {P : C} (hP : ObjectProperty.flat P) {P' : D} (φ : P ⟶ g.obj P')
    [IsIso ((adj.homEquiv _ _).symm φ)] :
    IsIso (ShortComplex.ShortExact.singleTranspose g
      adj.derivedAdjunctionMapDerivedCategory φ) := by
  rw [adj.singleTranspose_derivedAdjunctionMapDerivedCategory hP]
  infer_instance

end CategoryTheory
