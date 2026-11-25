/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOrdinaryEvaluationComparisons
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenArrows
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor

/-!
# Unit normalization of ordinary open realization

Source: Zheng, Constructions 4.1 and 4.22 (4.22.1); Stacks, Tags 03DI and 09AE.
This is the one-open-adjunction normalization used before taking cartesian mates
(blueprint: lem-sp-varying-ring-ordinary-open-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.VaryingRing
variable (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)
attribute [local instance 2000] WeilConjectures.SemilinearSections.sequenceSmall
  StrictTower.towers_hasDerivedCategory Scheme.proEtaleRingModules_hasDerivedCategory

attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor ordinaryRealization
  StrictTower.towers_hasDerivedCategory Scheme.proEtaleRingModules_hasDerivedCategory

section Recover
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  {F G : C ⥤ D} [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

private theorem recover_derived_iso (e : F ≅ G) :
    ordinaryRecoverSingleIso F G (Functor.mapDerivedCategoryNatIso e) = e := by
  apply Iso.ext
  apply ((Functor.FullyFaithful.ofFullyFaithful
    (DerivedCategory.singleFunctor D 0)).whiskeringRight C).map_injective
  ext M
  simp only [ordinaryRecoverSingleIso, Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, NatTrans.comp_app]
  change (F.mapDerivedCategorySingleFunctor 0).inv.app M ≫
    (Functor.mapDerivedCategoryNatIso e).hom.app
      ((DerivedCategory.singleFunctor C 0).obj M) ≫
    (G.mapDerivedCategorySingleFunctor 0).hom.app M =
      (DerivedCategory.singleFunctor D 0).map (e.hom.app M)
  rw [Functor.mapDerivedCategoryNatIso_hom_app_singleFunctor,
    Iso.inv_hom_id_app_assoc]

end Recover

private def ordinaryOpenInverse (n : ℕ) {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    eval R φ U n ⋙ StrictTower.moduleJ (R n) j ≅ extension R φ j ⋙ eval R φ X n := by
  have := ordinaryOpenMateIso R φ j n
  exact asIso ((mateEquiv (moduleJAdj R φ j)
    (StrictTower.moduleJAdj (R n) j)).symm (moduleEvalG R φ j n).hom)

private theorem ordinaryOpenInverse_unit (n : ℕ) {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (N : Modules R φ U) :
    (StrictTower.moduleJAdj (R n) j).unit.app ((eval R φ U n).obj N) ≫
        (StrictTower.modulePullback (R n) j).map
          ((ordinaryOpenInverse R φ n j).hom.app N) =
      (eval R φ U n).map ((moduleJAdj R φ j).unit.app N) ≫
        (moduleEvalG R φ j n).hom.app ((extension R φ j).obj N) := by
  exact (unit_mateEquiv_symm (moduleJAdj R φ j)
    (StrictTower.moduleJAdj (R n) j) (moduleEvalG R φ j n).hom N).symm

private theorem evalJ_inverse_localized (n : ℕ) {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    evalJ R φ j n =
      (Functor.mapDerivedCategorySquareIso (ordinaryOpenInverse R φ n j)).symm := by
  have hd := StrictTower.exact_mate (moduleJAdj R φ j)
    (StrictTower.moduleJAdj (R n) j) (moduleEvalG R φ j n)
    (ordinaryOpenInverse R φ n j) (jAdj R φ j) (levelJAdj R j n)
    (by simpa only [StrictTower.exactAdj, jAdj] using
      StrictTower.exactAdj_unit (moduleJAdj R φ j))
    (by simpa only [StrictTower.exactAdj, levelJAdj] using
      StrictTower.exactAdj_unit (StrictTower.moduleJAdj (R n) j))
    (ordinaryOpenInverse_unit R φ n j)
  have he : evalJInv R φ j n =
      (Functor.mapDerivedCategorySquareIso (ordinaryOpenInverse R φ n j)).hom := by
    ext M
    apply ((levelJAdj R j n).homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    exact (unit_mateEquiv_symm (jAdj R φ j) (levelJAdj R j n)
      (evalG R φ j n).hom M).symm.trans (hd M).symm
  apply Iso.ext_inv
  exact he

private theorem ordinaryOpenEvaluation_inverse (n : ℕ) {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    ordinaryOpenEvaluation R φ n j = (ordinaryOpenInverse R φ n j).symm := by
  unfold ordinaryOpenEvaluation
  rw [evalJ_inverse_localized]
  have he : (Functor.mapDerivedCategoryCompIso (extension R φ j) (eval R φ X n)).symm ≪≫
      (Functor.mapDerivedCategorySquareIso (ordinaryOpenInverse R φ n j)).symm ≪≫
      Functor.mapDerivedCategoryCompIso (eval R φ U n)
        (StrictTower.moduleJ (R n) j) =
      Functor.mapDerivedCategoryNatIso (ordinaryOpenInverse R φ n j).symm := by
    apply Iso.ext
    simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, Category.assoc, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id, Category.comp_id]
    exact (Functor.mapDerivedCategoryNatIso_symm (ordinaryOpenInverse R φ n j)).symm
  rw [he, recover_derived_iso]

private theorem ordinaryOpenEvaluation_mate (n : ℕ) {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    mateEquiv (moduleJAdj R φ j) (StrictTower.moduleJAdj (R n) j)
      (ordinaryOpenEvaluation R φ n j).inv = (moduleEvalG R φ j n).hom := by
  rw [ordinaryOpenEvaluation_inverse]
  exact (mateEquiv (moduleJAdj R φ j)
    (StrictTower.moduleJAdj (R n) j)).apply_symm_apply _

private theorem factorsh_complex {E F' : Type*} [Category E] [Category F'] [Abelian E] [Abelian F']
    [HasDerivedCategory E] [HasDerivedCategory F']
    (H : E ⥤ F') [H.Additive] [PreservesFiniteLimits H]
    [PreservesFiniteColimits H] (K : CochainComplex E ℤ) :
    H.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient E (.up ℤ)).obj K) =
    H.mapDerivedCategoryFactors.hom.app K := by
  rw [H.mapDerivedCategoryFactorsh_hom_app]
  change H.mapDerivedCategory.map (𝟙 (DerivedCategory.Q.obj K)) ≫
    H.mapDerivedCategoryFactors.hom.app K ≫
    𝟙 (DerivedCategory.Q.obj ((H.mapHomologicalComplex (.up ℤ)).obj K)) ≫
    DerivedCategory.Qh.map (𝟙 ((HomotopyCategory.quotient F' (.up ℤ)).obj
      ((H.mapHomologicalComplex (.up ℤ)).obj K))) = _
  erw [H.mapDerivedCategory.map_id, (DerivedCategory.Qh (C := F')).map_id]
  change 𝟙 _ ≫ H.mapDerivedCategoryFactors.hom.app K ≫
    𝟙 (DerivedCategory.Q.obj ((H.mapHomologicalComplex (.up ℤ)).obj K)) ≫
    𝟙 (DerivedCategory.Q.obj ((H.mapHomologicalComplex (.up ℤ)).obj K)) = _
  simp only [Category.id_comp, Category.comp_id]
  exact Category.comp_id _
private theorem single_unit_term
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) (G : D ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (adj : F ⊣ G) (X : C) :
    (DerivedCategory.singleFunctor C 0).map (adj.unit.app X) ≫
      (G.mapDerivedCategorySingleFunctor 0).inv.app (F.obj X) ≫
      G.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).inv.app X ≫
        F.mapDerivedCategoryFactorsh.hom.app
          ((HomotopyCategory.quotient C (.up ℤ)).obj
            ((CochainComplex.singleFunctor C 0).obj X))) ≫
      G.mapDerivedCategoryFactorsh.hom.app
        ((F.mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient C (.up ℤ)).obj
            ((CochainComplex.singleFunctor C 0).obj X))) =
      DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).unit.app
        ((HomotopyCategory.quotient C (.up ℤ)).obj
          ((CochainComplex.singleFunctor C 0).obj X))) := by
  rw [adj.mapHomotopyCategory_unit_app_quotient (.up ℤ)]
  rw [factorsh_complex F]
  change (DerivedCategory.singleFunctor C 0).map (adj.unit.app X) ≫
    (G.mapDerivedCategorySingleFunctor 0).inv.app (F.obj X) ≫
    G.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).inv.app X ≫
      F.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor C 0).obj X)) ≫
    G.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient D (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj ((CochainComplex.singleFunctor C 0).obj X))) = _
  rw [factorsh_complex G]
  erw [Functor.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app]
  erw [Functor.mapDerivedCategoryFactors_hom_naturality]
  erw [Functor.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app_assoc]
  change DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _ =
    DerivedCategory.Q.map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  apply HomologicalComplex.hom_ext
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [CochainComplex.singleFunctor, CochainComplex.singleFunctors, Functor.comp_obj,
      CochainComplex.shiftFunctor_obj_X', Functor.id_obj, Functor.mapCochainComplexSingleFunctor,
      HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
      HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
      eqToIso_refl, Iso.refl_hom, Iso.refl_inv, Category.id_comp,
      Adjunction.mapHomologicalComplex_unit_app_f,
      HomologicalComplex.single_map_f_self]
    change (adj.unit.app X ≫ 𝟙 _) ≫ G.map (𝟙 (F.obj X)) ≫
      G.map (F.map (𝟙 X)) = adj.unit.app X
    simp only [F.map_id, G.map_id, Category.comp_id]
    exact Category.comp_id _
  · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 X n hn).eq_of_src _ _

section SingleMate
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions D]
  {L : C ⥤ D} {P : D ⥤ C} [L.Additive] [P.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]

private theorem single_unit (a : L ⊣ P) (M : C) :
    (StrictTower.exactAdj a).unit.app ((DerivedCategory.singleFunctor C 0).obj M) ≫
      P.mapDerivedCategory.map ((L.mapDerivedCategorySingleFunctor 0).hom.app M) ≫
      (P.mapDerivedCategorySingleFunctor 0).hom.app (L.obj M) =
    (DerivedCategory.singleFunctor C 0).map (a.unit.app M) := by
  let K := (HomotopyCategory.quotient C (.up ℤ)).obj
    ((CochainComplex.singleFunctor C 0).obj M)
  have hm := StrictTower.exactAdj_unit a K
  have ht := single_unit_term L P a M
  have hc : (StrictTower.exactAdj a).unit.app (DerivedCategory.Qh.obj K) ≫
      P.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app K) =
    (DerivedCategory.singleFunctor C 0).map (a.unit.app M) ≫
      (P.mapDerivedCategorySingleFunctor 0).inv.app (L.obj M) ≫
      P.mapDerivedCategory.map ((L.mapDerivedCategorySingleFunctor 0).inv.app M) ≫
      P.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app K) :=
    (cancel_mono (P.mapDerivedCategoryFactorsh.hom.app
      ((L.mapHomotopyCategory (.up ℤ)).obj K))).mp
      (by simpa only [Functor.comp_obj, Functor.id_obj, K, Functor.map_comp,
        Category.assoc] using hm.trans ht.symm)
  have hu : (StrictTower.exactAdj a).unit.app (DerivedCategory.Qh.obj K) =
    (DerivedCategory.singleFunctor C 0).map (a.unit.app M) ≫
      (P.mapDerivedCategorySingleFunctor 0).inv.app (L.obj M) ≫
      P.mapDerivedCategory.map ((L.mapDerivedCategorySingleFunctor 0).inv.app M) :=
    (cancel_mono (P.mapDerivedCategory.map
      (L.mapDerivedCategoryFactorsh.hom.app K))).mp
      (by simpa only [Category.assoc] using hc)
  change (StrictTower.exactAdj a).unit.app (DerivedCategory.Qh.obj K) ≫ _ ≫ _ = _
  rw [hu]
  simp only [Functor.comp_obj, Category.assoc, ← Functor.map_comp_assoc,
    Iso.inv_hom_id_app, P.mapDerivedCategory.map_id, Category.id_comp]
  exact Category.comp_id _

private theorem single_mate (a : L ⊣ P) :
    mateEquiv a (StrictTower.exactAdj a) (L.mapDerivedCategorySingleFunctor 0).hom =
      (P.mapDerivedCategorySingleFunctor 0).inv := by
  apply mateEquiv_eq_of_unit
  intro M
  apply (cancel_mono ((P.mapDerivedCategorySingleFunctor 0).hom.app (L.obj M))).mp
  simp only [Category.assoc, Iso.inv_hom_id_app]
  simpa only [Functor.comp_obj, Category.comp_id] using (single_unit a M).symm

end SingleMate

private theorem constant_mate
    {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {P : D ⥤ C} (a : L ⊣ P) :
    mateEquiv a (a.whiskerRight ℕᵒᵖ) (Functor.compConstIso ℕᵒᵖ L).inv =
      (Functor.compConstIso ℕᵒᵖ P).hom := by
  apply mateEquiv_eq_of_unit
  intro M
  ext k
  simp [Functor.compConstIso, Adjunction.whiskerRight]

private theorem constantSingle_mate
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [hC : HasDerivedCategory (ℕᵒᵖ ⥤ C)] [hD : HasDerivedCategory (ℕᵒᵖ ⥤ D)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ D)]
    {L : C ⥤ D} {P : D ⥤ C} [L.Additive] [P.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ C D).obj L)]
    [PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ C D).obj L)]
    [PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ D C).obj P)]
    [PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ D C).obj P)]
    (a : L ⊣ P) :
    mateEquiv a (StrictTower.exactAdj (a.whiskerRight ℕᵒᵖ))
      (ordinaryConstantSingleComparison L).inv =
      (ordinaryConstantSingleComparison P).hom := by
  have h := mateEquiv_vcomp a (a.whiskerRight ℕᵒᵖ)
    (StrictTower.exactAdj (a.whiskerRight ℕᵒᵖ))
    (TwoSquare.mk _ _ _ _ (Functor.compConstIso ℕᵒᵖ L).inv)
    (TwoSquare.mk _ _ _ _
      (((Functor.whiskeringRight ℕᵒᵖ C D).obj L).mapDerivedCategorySingleFunctor 0).hom)
  rw [constant_mate, single_mate] at h
  refine NatTrans.ext (funext fun N ↦ ?_)
  have he := congrArg (fun t ↦ t.app N) h
  simpa only [ordinaryConstantSingleComparison, TwoSquare.hComp, TwoSquare.vComp,
    TwoSquare.mk, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.map_id, Category.id_comp, Category.comp_id, Category.assoc] using he

private theorem strictConstantSingle_mate (B : CommRingCat.{u + 1})
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    mateEquiv (StrictTower.moduleJAdj B j) (StrictTower.jAdj B j)
      (ordinaryConstantSingleComparison (StrictTower.moduleJ B j)).inv =
      (ordinaryConstantSingleComparison (StrictTower.modulePullback B j)).hom := by
  rw [← StrictTower.exactAdj_jAdj B j]
  exact constantSingle_mate
    (hC := StrictTower.towers_hasDerivedCategory B U)
    (hD := StrictTower.towers_hasDerivedCategory B X)
    (StrictTower.moduleJAdj B j)

section PasteComparison
variable {A B C D E F : Type*}
  [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
  {L₁ : A ⥤ B} {G : A ⥤ C} {H : B ⥤ D} {L₂ : C ⥤ D}
  {I : C ⥤ E} {J : D ⥤ F} {L₃ : E ⥤ F} {EA : A ⥤ E} {EB : B ⥤ F}

private def pasteComparison (α : L₁ ⋙ H ≅ G ⋙ L₂) (β : L₂ ⋙ J ≅ I ⋙ L₃)
    (eA : EA ≅ G ⋙ I) (eB : EB ≅ H ⋙ J) : L₁ ⋙ EB ≅ EA ⋙ L₃ :=
  Functor.isoWhiskerLeft _ eB ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight α _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ β ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight eA.symm _

private theorem pasteComparison_inv (α : L₁ ⋙ H ≅ G ⋙ L₂) (β : L₂ ⋙ J ≅ I ⋙ L₃)
    (eA : EA ≅ G ⋙ I) (eB : EB ≅ H ⋙ J) :
    (pasteComparison α β eA eB).inv =
      (((TwoSquare.mk _ _ _ _ α.inv).hComp
        (TwoSquare.mk _ _ _ _ β.inv)).whiskerTop eA.hom).whiskerBottom eB.inv := by
  refine NatTrans.ext (funext fun N ↦ ?_)
  simp only [pasteComparison, TwoSquare.hComp,
    TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.mk,
    Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.assoc]

private theorem pasteComparison_hom (α : L₁ ⋙ H ≅ G ⋙ L₂) (β : L₂ ⋙ J ≅ I ⋙ L₃)
    (eA : EA ≅ G ⋙ I) (eB : EB ≅ H ⋙ J) :
    (pasteComparison α β eA eB).hom =
      (((TwoSquare.mk _ _ _ _ α.hom).vComp
        (TwoSquare.mk _ _ _ _ β.hom)).whiskerRight eB.hom).whiskerLeft eA.inv := by
  refine NatTrans.ext (funext fun N ↦ ?_)
  simp only [pasteComparison, TwoSquare.vComp,
    TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.mk,
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.assoc]

end PasteComparison

/-- The inverse open comparison is the mate of the specified pullback comparison.
Source: Zheng, Constructions 4.1 and 4.22 (4.22.1); Stacks, Tags 03DI and 09AE
(blueprint: lem-sp-varying-ring-ordinary-open-unit).
Proof: the inverse derived evaluation comparison evalJInv is defined as the inverse
mate of evalG. Recover this unit equation through the fully faithful degree-zero
embedding, using the exact-single naturality and composition equations. Apply the
constant-tower functor termwise to the ordinary unit equation. The exact-single
comparison transports this to the derived strict open adjunction, because the latter
is the localization of the termwise ordinary adjunction. Finally conjugate by the
ordinaryRealization_eq equality isomorphisms. Naturality cancels these transports.
Explicitly, writing E for realization, g for the pullback comparison, and e for the
open comparison, the resulting unit equation on N is
E_U.map(eta_N) ; g.hom_(j_! N) = eta'_(E_U N) ; G_j.map(e.inv_N).
The unit characterization of mateEquiv identifies its unique mate with g.hom,
which is the displayed equality. No cartesian square is involved. -/
theorem ordinaryOpen_mate (n : ℕ) {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    mateEquiv (moduleJAdj R φ j) (StrictTower.jAdj (R n) j)
      (ordinaryOpenComparison R φ n U X j).inv =
      (ordinaryPullComparison R φ n U X j).hom := by
  let α := TwoSquare.mk _ _ _ _ (ordinaryOpenEvaluation R φ n j).inv
  let β := TwoSquare.mk _ _ _ _
    (ordinaryConstantSingleComparison (StrictTower.moduleJ (R n) j)).inv
  let eU := eqToIso (ordinaryRealization_eq R φ n U)
  let eX := eqToIso (ordinaryRealization_eq R φ n X)
  have hβ := strictConstantSingle_mate (R n) j
  have hm := mateEquiv_vcomp (moduleJAdj R φ j)
    (StrictTower.moduleJAdj (R n) j) (StrictTower.jAdj (R n) j) α β
  change mateEquiv (moduleJAdj R φ j) (StrictTower.jAdj (R n) j) (α.hComp β) =
    (mateEquiv (moduleJAdj R φ j) (StrictTower.moduleJAdj (R n) j)
      (ordinaryOpenEvaluation R φ n j).inv).vComp
    (mateEquiv (StrictTower.moduleJAdj (R n) j) (StrictTower.jAdj (R n) j)
      (ordinaryConstantSingleComparison (StrictTower.moduleJ (R n) j)).inv) at hm
  rw [ordinaryOpenEvaluation_mate, hβ] at hm
  calc
    _ = mateEquiv (moduleJAdj R φ j) (StrictTower.jAdj (R n) j)
        (((α.hComp β).whiskerTop eU.hom).whiskerBottom eX.inv) := by
      apply congrArg (mateEquiv (moduleJAdj R φ j) (StrictTower.jAdj (R n) j))
      exact pasteComparison_inv (ordinaryOpenEvaluation R φ n j)
        (ordinaryConstantSingleComparison (StrictTower.moduleJ (R n) j)) eU eX
    _ = _ := by
      rw [mateEquiv_whiskerTop_whiskerBottom, hm]
      exact (pasteComparison_hom (moduleEvalG R φ j n)
        (ordinaryConstantSingleComparison (StrictTower.modulePullback (R n) j)) eX eU).symm

end AlgebraicGeometry.ProEtale.VaryingRing
