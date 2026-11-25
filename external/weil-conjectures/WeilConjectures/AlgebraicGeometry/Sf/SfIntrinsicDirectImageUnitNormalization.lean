/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

/-! # All-complex normalization of the inverse realization/direct-image comparison

## References

* Stacks Tags 0D6E and 07A6
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  AlgebraicGeometry.Scheme.sfIntrinsicModuleEquivalence
attribute [local implicit_reducible] Equivalence.mapDerivedCategory
  AlgebraicGeometry.Scheme.sfIntrinsicDerivedEquivalence

-- Naturality extends a unit equation from K-injective representatives to complexes.
private theorem normalized_of_kInjectives
    {C D C' D' : Type*}
    [Category C] [Category D] [Category C'] [Category D']
    [Abelian C] [Abelian D] [Abelian C'] [Abelian D']
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory C'] [HasDerivedCategory D']
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions C']
    (F : C ⥤ D) (G : C' ⥤ D') (x : C ⥤ C') (y : D ⥤ D')
    [F.Additive] [G.Additive] [x.Additive] [y.Additive]
    [PreservesFiniteLimits x] [PreservesFiniteColimits x]
    [PreservesFiniteLimits y] [PreservesFiniteColimits y]
    (c : F ⋙ y ⟶ x ⋙ G)
    (b : F.rightDerivedFunctor ⋙ y.mapDerivedCategory ⟶
      x.mapDerivedCategory ⋙ G.rightDerivedFunctor)
    (h : ∀ (I : CochainComplex C ℤ) [I.IsKInjective],
      y.mapDerivedCategory.map (F.rightDerivedFunctorUnitQ I) ≫
          b.app (DerivedCategory.Q.obj I) ≫
          G.rightDerivedFunctor.map (x.mapDerivedCategoryFactors.hom.app I) =
        y.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex c (.up ℤ)).app I) ≫
          G.rightDerivedFunctorUnitQ ((x.mapHomologicalComplex (.up ℤ)).obj I)) :
    ∀ I : CochainComplex C ℤ,
      y.mapDerivedCategory.map (F.rightDerivedFunctorUnitQ I) ≫
          b.app (DerivedCategory.Q.obj I) ≫
          G.rightDerivedFunctor.map (x.mapDerivedCategoryFactors.hom.app I) =
        y.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex c (.up ℤ)).app I) ≫
          G.rightDerivedFunctorUnitQ ((x.mapHomologicalComplex (.up ℤ)).obj I) := by
  let unitF : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
    ⟨F.rightDerivedFunctorUnitQ, fun _ _ f ↦ F.rightDerivedFunctorUnitQ_naturality f⟩
  let unitG : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ G.rightDerivedFunctor :=
    ⟨G.rightDerivedFunctorUnitQ, fun _ _ f ↦ G.rightDerivedFunctorUnitQ_naturality f⟩
  let a := Functor.whiskerRight unitF y.mapDerivedCategory ≫
    Functor.whiskerLeft DerivedCategory.Q b
  let a' := Functor.whiskerLeft (F.mapHomologicalComplex (.up ℤ))
      y.mapDerivedCategoryFactors.hom ≫
    Functor.whiskerRight (NatTrans.mapHomologicalComplex c (.up ℤ)) DerivedCategory.Q ≫
    Functor.whiskerLeft (x.mapHomologicalComplex (.up ℤ)) unitG ≫
    Functor.whiskerRight x.mapDerivedCategoryFactors.inv G.rightDerivedFunctor
  have hi (I : CochainComplex C ℤ) [I.IsKInjective] : a.app I = a'.app I := by
    apply (cancel_mono (G.rightDerivedFunctor.map
      (x.mapDerivedCategoryFactors.hom.app I))).mp
    simpa only [a, a', unitF, unitG, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Category.assoc, ← G.rightDerivedFunctor.map_comp,
      Iso.inv_hom_id_app, Functor.map_id, G.rightDerivedFunctor.map_id,
      Functor.comp_obj, Category.comp_id] using h I
  intro M
  have hm : a.app M = a'.app M := by
    obtain ⟨I, _, j, _, _⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective M
    have : IsIso (DerivedCategory.Q.map j) := inferInstance
    have : IsIso ((DerivedCategory.Q ⋙ x.mapDerivedCategory ⋙ G.rightDerivedFunctor).map j) := by
      change IsIso (G.rightDerivedFunctor.map (x.mapDerivedCategory.map
        (DerivedCategory.Q.map j)))
      infer_instance
    apply (cancel_mono
      ((DerivedCategory.Q ⋙ x.mapDerivedCategory ⋙ G.rightDerivedFunctor).map j)).mp
    exact (a.naturality j).symm.trans
      ((congrArg (fun z ↦ ((F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) ⋙
        y.mapDerivedCategory).map j ≫ z) (hi I)).trans (a'.naturality j))
  have hh := congrArg (fun z ↦ z ≫
    G.rightDerivedFunctor.map (x.mapDerivedCategoryFactors.hom.app M)) hm
  simpa only [a, a', unitF, unitG, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.assoc, ← G.rightDerivedFunctor.map_comp,
    Iso.inv_hom_id_app, Functor.map_id, G.rightDerivedFunctor.map_id,
      Functor.comp_obj, Category.comp_id] using hh

namespace AlgebraicGeometry.Scheme

private theorem invert_normalization
    {C : Type*} [Category C] {X Y Z W V U : C}
    (d : X ≅ Y) (q : Y ≅ Z) (e : Z ≅ W)
    (x : X ≅ V) (p : V ≅ U) (a : U ≅ W)
    (h : d.hom ≫ q.hom ≫ e.hom = x.hom ≫ p.hom ≫ a.hom) :
    q.inv ≫ d.inv ≫ x.hom = e.hom ≫ a.inv ≫ p.inv := by
  apply (cancel_epi (d.hom ≫ q.hom)).mp
  apply (cancel_mono (p.hom ≫ a.hom)).mp
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id, Category.comp_id] using h.symm

private theorem inverse_normalization_at
    {C D C' D' : Type*}
    [Category C] [Category D] [Category C'] [Category D']
    [Abelian C] [Abelian D] [Abelian C'] [Abelian D']
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory C'] [HasDerivedCategory D']
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions C']
    (F : C ⥤ D) (G : C' ⥤ D') (x : C ⥤ C') (y : D ⥤ D')
    [F.Additive] [G.Additive] [x.Additive] [y.Additive]
    [PreservesFiniteLimits x] [PreservesFiniteColimits x]
    [PreservesFiniteLimits y] [PreservesFiniteColimits y]
    (c : x ⋙ G ≅ F ⋙ y)
    (d : x.mapDerivedCategory ⋙ G.rightDerivedFunctor ≅
      F.rightDerivedFunctor ⋙ y.mapDerivedCategory)
    (J : CochainComplex C ℤ) [J.IsKInjective]
    [CochainComplex.IsKInjective ((x.mapHomologicalComplex (.up ℤ)).obj J)]
    (hn : d.hom.app (DerivedCategory.Q.obj J) ≫
      y.mapDerivedCategory.map (F.rightDerivedFunctorObjQIso J).hom ≫
      y.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj J) =
      G.rightDerivedFunctor.map (x.mapDerivedCategoryFactors.hom.app J) ≫
      (G.rightDerivedFunctorObjQIso ((x.mapHomologicalComplex (.up ℤ)).obj J)).hom ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app J)) :
    y.mapDerivedCategory.map (F.rightDerivedFunctorUnitQ J) ≫
      d.inv.app (DerivedCategory.Q.obj J) ≫
      G.rightDerivedFunctor.map (x.mapDerivedCategoryFactors.hom.app J) =
    y.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj J) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex c.inv (.up ℤ)).app J) ≫
      G.rightDerivedFunctorUnitQ ((x.mapHomologicalComplex (.up ℤ)).obj J) := by
  rw [Functor.rightDerivedFunctorUnitQ_eq, Functor.rightDerivedFunctorUnitQ_eq]
  exact invert_normalization (d.app (DerivedCategory.Q.obj J))
    (y.mapDerivedCategory.mapIso (F.rightDerivedFunctorObjQIso J))
    (y.mapDerivedCategoryFactors.app ((F.mapHomologicalComplex (.up ℤ)).obj J))
    (G.rightDerivedFunctor.mapIso (x.mapDerivedCategoryFactors.app J))
    (G.rightDerivedFunctorObjQIso ((x.mapHomologicalComplex (.up ℤ)).obj J))
    (DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex c (.up ℤ)).app J)) hn

private theorem realization_kInjective
    (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    (J : CochainComplex
      (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ℤ)
    [J.IsKInjective] :
    CochainComplex.IsKInjective
      (((sfIntrinsicModuleEquivalence T A).functor.mapHomologicalComplex (.up ℤ)).obj J) := by
  infer_instance

/-- The inverse realization/direct-image comparison has its canonical complex-unit
normalization on every complex. -/
theorem sfIntrinsicDerivedDirectImageComparison_inv_unitQ_factors
    (A : Type u) [CommRing A] [Finite A] {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    ∀ J : CochainComplex
      (Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ℤ,
    (sfIntrinsicModuleEquivalence Y A).functor.mapDerivedCategory.map
        (Functor.rightDerivedFunctorUnitQ
          (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g) J) ≫
      (sfIntrinsicDerivedDirectImageComparison g A).inv.app (DerivedCategory.Q.obj J) ≫
      (proEtaleConstantModuleDirectImage g A).rightDerivedFunctor.map
        ((sfIntrinsicModuleEquivalence Z A).functor.mapDerivedCategoryFactors.hom.app J) =
    (sfIntrinsicModuleEquivalence Y A).functor.mapDerivedCategoryFactors.hom.app
        ((Functor.mapHomologicalComplex
          (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g) (.up ℤ)).obj J) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (sfIntrinsicDirectImageComparison g A).inv (.up ℤ)).app J) ≫
      (proEtaleConstantModuleDirectImage g A).rightDerivedFunctorUnitQ
        (((sfIntrinsicModuleEquivalence Z A).functor.mapHomologicalComplex (.up ℤ)).obj J) := by
  apply normalized_of_kInjectives
  intro J hJ
  let := realization_kInjective Z A J
  have hn := (sfIntrinsicDerivedDirectImageComparison_existsUnique g A).exists.choose_spec
    J
  exact inverse_normalization_at
    (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g)
    (proEtaleConstantModuleDirectImage g A)
    (sfIntrinsicModuleEquivalence Z A).functor
    (sfIntrinsicModuleEquivalence Y A).functor
    (sfIntrinsicDirectImageComparison g A)
    (sfIntrinsicDerivedDirectImageComparison g A) J hn

end AlgebraicGeometry.Scheme
