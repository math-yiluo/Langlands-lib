/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.BaseChangeStalkTransition
public import WeilConjectures.CategoryTheory.RightDerivedSingleUnitHomologyComparison
import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
open CategoryTheory Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
@[expose] public section
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem single_counit
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (adj : L ⊣ R) (J : D) :
    L.mapDerivedCategoryPlus.map (R.rightDerivedPlusSingleUnit J) ≫
        adj.derivedPlus.counit.app ((DerivedCategory.Plus.singleFunctor D 0).obj J) =
      (L.mapDerivedCategoryPlusSingleFunctor 0).hom.app (R.obj J) ≫
        (DerivedCategory.Plus.singleFunctor D 0).map (adj.counit.app J) := by
  let K := (HomotopyCategory.Plus.singleFunctor D 0).obj J
  have ht : (DerivedCategory.Plus.ι.preimageIso
      (X := (DerivedCategory.Plus.singleFunctor D 0).obj J)
      (Y := DerivedCategory.Plus.Qh.obj K)
      ((DerivedCategory.singleFunctorIsoCompQ D 0).app J ≪≫
        (DerivedCategory.quotientCompQhIso D).symm.app _)).inv = 𝟙 _ := by
    apply DerivedCategory.Plus.ι.map_injective
    simp only [Functor.preimageIso_inv, Functor.map_preimage, Iso.trans_inv]
    change (DerivedCategory.quotientCompQhIso D).hom.app _ ≫ 𝟙 _ = 𝟙 _
    rw [Category.comp_id]
    rfl
  dsimp only [Functor.rightDerivedPlusSingleUnit]
  rw [ht]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  rw [Functor.map_comp, Category.assoc]
  erw [adj.derivedPlus_counit_app_fac K]
  apply DerivedCategory.Plus.ι.map_injective
  simp only [Functor.map_comp,
    Functor.ι_map_mapDerivedCategoryPlusSingleFunctor_hom_app,
    Functor.ι_map_mapDerivedCategoryPlusFactorsh_hom_app]
  change L.mapDerivedCategory.map
      (DerivedCategory.Plus.ι.map (R.mapHomotopyCategoryPlusSingleFunctorQhObjIso 0 J).inv) ≫
      L.mapDerivedCategoryFactorsh.hom.app
        ((R.mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient D (.up ℤ)).obj
            ((CochainComplex.singleFunctor D 0).obj J))) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.Plus.ι D).map
        (adj.mapHomotopyCategoryPlus.counit.app K)) = _
  rw [Adjunction.ι_map_mapHomotopyCategoryPlus_counit_app]
  erw [Adjunction.mapHomotopyCategory_counit_app_quotient,
    Functor.mapDerivedCategoryFactorsh_hom_app]
  simp only [Functor.mapHomotopyCategoryPlusSingleFunctorQhObjIso,
    Functor.preimageIso_inv, Functor.map_preimage,
    Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv,
    Category.assoc]
  erw [CategoryTheory.Functor.map_id, Category.id_comp,
    CategoryTheory.Functor.map_id, Category.id_comp]
  erw [← DerivedCategory.quotientCompQhIso_inv_naturality]
  have hqi : (DerivedCategory.quotientCompQhIso D).inv.app
      ((CochainComplex.singleFunctor D 0).obj J) = 𝟙 _ := rfl
  erw [hqi, Category.comp_id]
  change L.mapDerivedCategory.map
      (DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) 0).inv.app J) ≫ 𝟙 _) ≫
      L.mapDerivedCategoryFactors.hom.app
        ((R.mapHomologicalComplex (.up ℤ)).obj ((CochainComplex.singleFunctor D 0).obj J)) ≫
      DerivedCategory.Q.map
        ((adj.mapHomologicalComplex (.up ℤ)).counit.app
          ((CochainComplex.singleFunctor D 0).obj J)) =
    (L.mapDerivedCategorySingleFunctor 0).hom.app (R.obj J) ≫
      (DerivedCategory.singleFunctor D 0).map (adj.counit.app J)
  rw [Category.comp_id]
  erw [Functor.mapDerivedCategoryFactors_hom_naturality_assoc]
  rw [← cancel_epi (L.mapDerivedCategoryFactors.inv.app
    ((CochainComplex.singleFunctor C 0).obj (R.obj J)))]
  erw [Iso.inv_hom_id_app_assoc]
  erw [Functor.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app_assoc]
  change DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _ =
    DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map
      ((CochainComplex.singleFunctor D 0).map (adj.counit.app J))
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  apply HomologicalComplex.hom_ext
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [CochainComplex.singleFunctor, Functor.comp_obj,
      Functor.id_obj, Functor.mapCochainComplexSingleFunctor,
      HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
      eqToIso_refl, Iso.refl_hom, Iso.refl_inv, Category.id_comp,
      Adjunction.mapHomologicalComplex_counit_app_f,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      HomologicalComplex.single_map_f_self]
    simp only [HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
    dsimp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]
    change L.map (𝟙 (R.obj J) ≫ R.map (𝟙 J)) ≫ adj.counit.app J =
      (L.map (𝟙 (R.obj J)) ≫ 𝟙 _) ≫ adj.counit.app J ≫ 𝟙 _
    simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  · simp [Functor.mapCochainComplexSingleFunctor,
      CochainComplex.singleFunctor,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_ne,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_ne, hn]

private lemma mate_fac
    {C₁ C₂ C₃ C₄ : Type*} [Category* C₁] [Category* C₂]
    [Category* C₃] [Category* C₄]
    {L : C₂ ⥤ C₁} {R : C₁ ⥤ C₂} {L' : C₄ ⥤ C₃} {R' : C₃ ⥤ C₄}
    {G : C₂ ⥤ C₄} {G' : C₁ ⥤ C₃}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (θ : TwoSquare G L L' G')
    {S : C₂} {X : C₁} (u : S ⟶ R.obj X) :
    G.map u ≫ (mateEquiv adj adj' θ).app X =
      adj'.unit.app (G.obj S) ≫
        R'.map (θ.app S ≫ G'.map (L.map u ≫ adj.counit.app X)) := by
  have hu := adj'.unit.naturality (G.map u)
  have ht := θ.naturality u
  simp only [Functor.id_map, Functor.comp_map] at hu ht
  have hm : (mateEquiv adj adj' θ).app X =
      adj'.unit.app (G.obj (R.obj X)) ≫ R'.map (θ.app (R.obj X)) ≫
        R'.map (G'.map (adj.counit.app X)) := by
    simp [mateEquiv_apply]
  rw [hm, ← Category.assoc, hu]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, ht]
  simp only [Functor.map_comp, Category.assoc]

private theorem derived_mate_single
    {C₁ C₂ C₃ C₄ : Type*} [Category* C₁] [Category* C₂]
    [Category* C₃] [Category* C₄]
    [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄]
    [HasDerivedCategory C₁] [HasDerivedCategory C₂]
    [HasDerivedCategory C₃] [HasDerivedCategory C₄]
    [EnoughInjectives C₁] [EnoughInjectives C₃]
    {L : C₂ ⥤ C₁} {R : C₁ ⥤ C₂} {L' : C₄ ⥤ C₃} {R' : C₃ ⥤ C₄}
    {G : C₂ ⥤ C₄} {G' : C₁ ⥤ C₃}
    [L.Additive] [R.Additive] [L'.Additive] [R'.Additive] [G.Additive] [G'.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
    (adj : L ⊣ R) (adj' : L' ⊣ R')
    (θ : TwoSquare G.mapDerivedCategoryPlus L.mapDerivedCategoryPlus
      L'.mapDerivedCategoryPlus G'.mapDerivedCategoryPlus) (J : C₁) :
    G.mapDerivedCategoryPlus.map (R.rightDerivedPlusSingleUnit J) ≫
      (mateEquiv adj.derivedPlus adj'.derivedPlus θ).app
        ((DerivedCategory.Plus.singleFunctor C₁ 0).obj J) =
      adj'.derivedPlus.unit.app (G.mapDerivedCategoryPlus.obj
        ((DerivedCategory.Plus.singleFunctor C₂ 0).obj (R.obj J))) ≫
        R'.rightDerivedFunctorPlus.map
          (θ.app ((DerivedCategory.Plus.singleFunctor C₂ 0).obj (R.obj J)) ≫
            G'.mapDerivedCategoryPlus.map
              ((L.mapDerivedCategoryPlusSingleFunctor 0).hom.app (R.obj J) ≫
                (DerivedCategory.Plus.singleFunctor C₁ 0).map (adj.counit.app J))) := by
  have h := mate_fac adj.derivedPlus adj'.derivedPlus θ (R.rightDerivedPlusSingleUnit J)
  rw [single_counit] at h
  exact h

universe u
namespace AlgebraicGeometry.Etale

/-- The derived mate calculation identifies the open injective coefficient map with the
ordinary base-change map on the coefficient `j_*J`. Source: Stacks Project, Tag 0F07,
closed-open lower comparison.
(blueprint: lem-sbc-open-injective-coefficient-lower-comparison-factorization)

Proof: rewrite `Etale.baseChange` by
`Etale.baseChange_eq_derivedBaseChangeMapPlus`, and then use the mate computation
`Adjunction.derivedPlus_mateEquiv_app_fac` for the pullback comparison.  On the
single complex containing `j_*J`, the exact pullback comparison is
`mapDerivedCategoryPlusSingleFunctor 0`; composing it with the counit of
`j^* ⊣ j_*` is the displayed final factor.  Naturality of the derived unit and
the two adjunction triangle identities then identify the resulting mate with
the left-hand composite.  Applying the homology functor preserves this equality.
-/
theorem open_injective_coefficient_lower_comparison_factorization
    (Λ : Type (u + 1)) [CommRing Λ]
    {Y T V W : Scheme.{u}}
    (e : Y ⟶ T) (j : V ⟶ T) (eV : W ⟶ V) (a : W ⟶ Y)
    [IsOpenImmersion j] [QuasiCompact j] [QuasiSeparated j]
    (wa : a ≫ e = eV ≫ j) (sq : IsPullback eV a j e)
    (n : ℤ) (J : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective J] :
    ((DerivedCategory.Plus.homologyFunctor _ n).map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a).derivedPlus.unit.app
        (D+((e)^*[ModuleCat.{u + 1} Λ]).obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj
              (((j)_*[ModuleCat.{u + 1} Λ]).obj J))) ≫
        R+((a)_*[ModuleCat.{u + 1} Λ]).map
          ((upperStarPlusComp (ModuleCat.{u + 1} Λ) a e).inv.app _ ≫
            eqToHom (by rw [wa]) ≫
            (upperStarPlusComp (ModuleCat.{u + 1} Λ) eV j).hom.app _ ≫
            D+((eV)^*[ModuleCat.{u + 1} Λ]).map
              ((((j)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
                (((j)_*[ModuleCat.{u + 1} Λ]).obj J) ≫
                (DerivedCategory.Plus.singleFunctor _ 0).map
                  ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).counit.app J))))) =
      (DerivedCategory.Plus.homologyFunctor _ n).map
        (D+((e)^*[ModuleCat.{u + 1} Λ]).map
            (CategoryTheory.Functor.rightDerivedPlusSingleUnit
              ((j)_*[ModuleCat.{u + 1} Λ]) J) ≫
          (Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app
            ((DerivedCategory.Plus.singleFunctor
              (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj J))  := by
  have h := derived_mate_single
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a)
    (TwoSquare.mk _ _ _ _ (pullbackSquareComparison (ModuleCat.{u + 1} Λ) sq.toCommSq).hom)
    J
  have hm := congrArg ((DerivedCategory.Plus.homologyFunctor _ n).map) h.symm
  rw [baseChange_app_eq_mateEquiv]
  simpa [pullbackSquareComparison, upperStarPlusComp] using hm
end AlgebraicGeometry.Etale
