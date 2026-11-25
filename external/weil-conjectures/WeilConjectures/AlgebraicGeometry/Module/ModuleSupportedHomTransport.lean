/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedHomCocycleNormalization
public import WeilConjectures.CategoryTheory.Derived.DerivedRepresentableTransport
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange

/-! # Module-valued transport of normalized supported Hom

## References

* Milne, Lectures on Etale Cohomology, Section 9, Ext proof of Theorem 9.4
* Stacks Tags 05TI and 070I
* Milne, Section 9, Ext proof of Theorem 9.4
* Stacks 015F and 070I
* Milne, Section 9, Ext proof of Theorem 9.4 and Example 9.5
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe uC uD uE vC vD vE wC wD wE

open CategoryTheory CategoryTheory.Limits Opposite

open CochainComplex.HomComplex

namespace CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {C : Type uC} {D : Type uD} {E : Type uE}
  [Category.{vC} C] [Category.{vD} D] [Category.{vE} E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
  [HasDerivedCategory.{wE} E] [EnoughInjectives C] [EnoughInjectives D]
  (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  (S : C ⥤ E) (S' : D ⥤ E) [S.Additive] [S'.Additive]
  (tau : S ⟶ L ⋙ S')
@[irreducible] private def normalizedSupportTransport :
    S.rightDerivedFunctorPlus ⟶ L.mapDerivedCategoryPlus ⋙ S'.rightDerivedFunctorPlus :=
  (Functor.rightUnitor _).inv ≫
    (Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryPlusIdIso E)).inv ≫
    Functor.rightDerivedFunctorPlusBaseChange
      (G := S) (G' := S') (β := L) (γ := 𝟭 E)
      ((Functor.rightUnitor _).hom ≫ tau)
private theorem normalizedSupportTransport_eq :
    normalizedSupportTransport L S S' tau =
      (Functor.rightUnitor _).inv ≫
        (Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryPlusIdIso E)).inv ≫
        Functor.rightDerivedFunctorPlusBaseChange
          (G := S) (G' := S') (β := L) (γ := 𝟭 E)
          ((Functor.rightUnitor _).hom ≫ tau) := by
  unfold normalizedSupportTransport
  rfl

private theorem normalizedSupportTransport_fac
    (I : CochainComplex.Plus C) :
    S.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient C).obj I) ≫
        (normalizedSupportTransport L S S' tau).app (DerivedCategory.Plus.Q.obj I) =
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus tau).app
        ((HomotopyCategory.Plus.quotient C).obj I)) ≫
      DerivedCategory.Plus.Qh.map
        ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (L ⋙ S'))).inv.app
          ((HomotopyCategory.Plus.quotient C).obj I)) ≫
      S'.rightDerivedFunctorPlusUnith.app
        (L.mapHomotopyCategoryPlus.obj ((HomotopyCategory.Plus.quotient C).obj I)) ≫
      S'.rightDerivedFunctorPlus.map
        (L.mapDerivedCategoryPlusFactorsh.inv.app
          ((HomotopyCategory.Plus.quotient C).obj I)) := by
  let M := (HomotopyCategory.Plus.quotient C).obj I
  have h := congr_app (rightDerivedFunctorPlusBaseChange_fac
    (G := S) (G' := S') (β := L) (γ := 𝟭 E)
    ((Functor.rightUnitor _).hom ≫ tau)) M
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    Functor.associator_hom_app, Category.comp_id] at h
  unfold normalizedSupportTransport
  dsimp only [NatTrans.comp_app, Functor.rightUnitor_inv_app,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Category.id_comp]
  have hr := (mapDerivedCategoryPlusIdIso E).inv.naturality
    (S.rightDerivedFunctorPlusUnith.app M)
  simp only [Functor.id_map] at hr
  simp only [Category.id_comp]
  erw [reassoc_of% hr, h]
  simp only [rightDerivedFunctorPlusBaseChangeAux, NatTrans.comp_app,
    whiskerLeft_app, whiskerRight_app, Functor.associator_inv_app,
    Functor.associator_hom_app, Category.id_comp, Category.comp_id]
  have hi := mapDerivedCategoryPlusIdIso_hom_app_factorsh E
    (S.mapHomotopyCategoryPlus.obj M)
  rw [← hi]
  simp only [Iso.inv_hom_id_app_assoc]
  simp only [← Functor.map_comp_assoc]
  congr 2
  simp only [NatTrans.mapHomotopyCategoryPlus_comp,
    NatTrans.comp_app, mapHomotopyCategoryPlusCompIso_refl_hom_app,
    Category.id_comp]
  have hu : (NatTrans.mapHomotopyCategoryPlus S.rightUnitor.hom).app M = 𝟙 _ := by
    exact NatTrans.mapHomotopyCategoryPlus_rightUnitor_hom_app S M
  rw [hu, Category.id_comp]

private def normalizedSupportChainMap
    (I : CochainComplex.Plus C) (J : CochainComplex.Plus D)
    (t : (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj ⟶ J.obj) :
    S.mapCochainComplexPlus.obj I ⟶ S'.mapCochainComplexPlus.obj J :=
  ObjectProperty.homMk
    ((NatTrans.mapHomologicalComplex tau (ComplexShape.up ℤ)).app I.obj ≫
      (mapHomologicalComplexCompIso (Iso.refl (L ⋙ S')) (ComplexShape.up ℤ)).inv.app
        I.obj ≫
      (S'.mapHomologicalComplex (ComplexShape.up ℤ)).map t)
omit [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [EnoughInjectives C] [EnoughInjectives D]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L] in
private theorem normalizedSupportChainMap_f
    (I : CochainComplex.Plus C) (J : CochainComplex.Plus D)
    (t : (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj ⟶ J.obj) (n : ℤ) :
    (normalizedSupportChainMap L S S' tau I J t).hom.f n =
      tau.app (I.obj.X n) ≫ S'.map (t.f n) := by
  simp only [normalizedSupportChainMap, ObjectProperty.homMk_hom,
    HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplex_map_f, Functor.mapHomologicalComplexCompIso,
    NatIso.mapHomologicalComplex, Iso.refl_inv]
  erw [Category.id_comp]

private theorem normalizedSupportTransport_model
    (I : CochainComplex.Plus C) (J : CochainComplex.Plus D)
    (e : L.mapCochainComplexPlus.obj I ⟶ J) :
    S.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient C).obj I) ≫
        (normalizedSupportTransport L S S' tau).app (DerivedCategory.Plus.Q.obj I) ≫
        S'.rightDerivedFunctorPlus.map (L.mapDerivedCategoryPlusFactorsh.hom.app
          ((HomotopyCategory.Plus.quotient C).obj I)) ≫
        S'.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map e) =
      DerivedCategory.Plus.Q.map (normalizedSupportChainMap L S S' tau I J e.hom) ≫
        S'.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient D).obj J) := by
  rw [reassoc_of% normalizedSupportTransport_fac L S S' tau I]
  simp only [← S'.rightDerivedFunctorPlus.map_comp]
  erw [Iso.inv_hom_id_app_assoc]
  have hn := S'.rightDerivedFunctorPlusUnith.naturality
    ((HomotopyCategory.Plus.quotient D).map e)
  simp only [Functor.comp_map] at hn
  erw [← hn]
  simp only [← Category.assoc, ← Functor.map_comp]
  congr 1
  change DerivedCategory.Plus.Qh.map _ = DerivedCategory.Plus.Qh.map
    ((HomotopyCategory.Plus.quotient E).map
      (normalizedSupportChainMap L S S' tau I J e.hom))
  congr 1
  apply (HomotopyCategory.Plus.ι E).map_injective
  simp only [Functor.map_comp, NatTrans.ι_map_mapHomotopyCategoryPlus_app,
    mapHomotopyCategoryPlusCompIso_refl_inv_app]
  simp only [CategoryTheory.Functor.map_id, Category.comp_id]
  change (HomotopyCategory.quotient E (ComplexShape.up ℤ)).map
      ((NatTrans.mapHomologicalComplex tau (ComplexShape.up ℤ)).app I.obj) ≫
        (HomotopyCategory.quotient E (ComplexShape.up ℤ)).map
          ((S'.mapHomologicalComplex (ComplexShape.up ℤ)).map e.hom) = _
  rw [← Functor.map_comp]
  congr 1
  ext n
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    mapHomologicalComplex_map_f, ObjectProperty.ι_map]
  exact (normalizedSupportChainMap_f L S S' tau I J e.hom n).symm

private theorem normalizedSupportTransport_homology
    (I : CochainComplex.Plus C) (J : CochainComplex.Plus D)
    (e : L.mapCochainComplexPlus.obj I ⟶ J) (a : ℤ) :
    (DerivedCategory.Plus.homologyFunctorObjQIso (S.mapCochainComplexPlus.obj I) a).inv ≫
        (DerivedCategory.Plus.homologyFunctor E a).map
          (S.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient C).obj I)) ≫
        (DerivedCategory.Plus.homologyFunctor E a).map
          ((normalizedSupportTransport L S S' tau).app (DerivedCategory.Plus.Q.obj I)) ≫
        (DerivedCategory.Plus.homologyFunctor E a).map
          (S'.rightDerivedFunctorPlus.map (L.mapDerivedCategoryPlusFactorsh.hom.app
            ((HomotopyCategory.Plus.quotient C).obj I))) ≫
        (DerivedCategory.Plus.homologyFunctor E a).map
          (S'.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map e)) =
      HomologicalComplex.homologyMap
          (normalizedSupportChainMap L S S' tau I J e.hom).hom a ≫
        (DerivedCategory.Plus.homologyFunctorObjQIso (S'.mapCochainComplexPlus.obj J) a).inv ≫
        (DerivedCategory.Plus.homologyFunctor E a).map
          (S'.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient D).obj J)) := by
  let H := DerivedCategory.Plus.homologyFunctor E a
  let c := normalizedSupportChainMap L S S' tau I J e.hom
  have hn := DerivedCategory.Plus.homologyFunctorObjQIso_hom_naturality c a
  have hs : (DerivedCategory.Plus.homologyFunctorObjQIso
      (S.mapCochainComplexPlus.obj I) a).inv ≫ H.map (DerivedCategory.Plus.Q.map c) =
      HomologicalComplex.homologyMap c.hom a ≫
        (DerivedCategory.Plus.homologyFunctorObjQIso (S'.mapCochainComplexPlus.obj J) a).inv := by
    apply (cancel_mono (DerivedCategory.Plus.homologyFunctorObjQIso
      (S'.mapCochainComplexPlus.obj J) a).hom).mp
    rw [Category.assoc, hn]
    simp only [Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change _ ≫ H.map _ ≫ H.map _ ≫ H.map _ ≫ H.map _ = _
  erw [← H.map_comp, ← H.map_comp, ← H.map_comp]
  erw [normalizedSupportTransport_model L S S' tau I J e]
  erw [H.map_comp, ← Category.assoc, hs]
  exact Category.assoc _ _ _

private theorem normalizedSupportTransport_homology_comp
    (I : CochainComplex.Plus C) (J : CochainComplex.Plus D)
    (e : L.mapCochainComplexPlus.obj I ⟶ J) (a : ℤ) :
    ((DerivedCategory.Plus.homologyFunctorObjQIso (S.mapCochainComplexPlus.obj I) a).inv ≫
        (DerivedCategory.Plus.homologyFunctor E a).map
          (S.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient C).obj I))) ≫
        (DerivedCategory.Plus.homologyFunctor E a).map
          ((normalizedSupportTransport L S S' tau).app (DerivedCategory.Plus.Q.obj I)) ≫
        (DerivedCategory.Plus.homologyFunctor E a).map
          (S'.rightDerivedFunctorPlus.map
            (L.mapDerivedCategoryPlusFactorsh.hom.app
              ((HomotopyCategory.Plus.quotient C).obj I) ≫ DerivedCategory.Plus.Q.map e)) =
      HomologicalComplex.homologyMap
          (normalizedSupportChainMap L S S' tau I J e.hom).hom a ≫
        ((DerivedCategory.Plus.homologyFunctorObjQIso (S'.mapCochainComplexPlus.obj J) a).inv ≫
          (DerivedCategory.Plus.homologyFunctor E a).map
            (S'.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient D).obj J))) := by
  rw [S'.rightDerivedFunctorPlus.map_comp,
    (DerivedCategory.Plus.homologyFunctor E a).map_comp]
  simpa only [Category.assoc] using normalizedSupportTransport_homology L S S' tau I J e a

end CategoryTheory.Functor

universe u
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CochainComplex

section
variable {A : Type (u + 1)} [CommRing A]
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J (ModuleCat.{u + 1} A)]
    [IsGrothendieckAbelian.{u + 1} (Sheaf J (ModuleCat.{u + 1} A))]
    {T W : C} (hT : IsTerminal T) (j : W ⟶ T)
    (B : Sheaf J (ModuleCat.{u + 1} A))
    (rho : (constantSheaf J (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A) ⟶ B)
private theorem supportHomResolutionIso_id
    (I : CochainComplex.Plus (Sheaf J (ModuleCat.{u + 1} A))) :
    supportedHomResolutionIso J A I I (𝟙 I) = Iso.refl _ := by
  apply Iso.ext
  apply DerivedCategory.Plus.ι.map_injective
  change DerivedCategory.Plus.ι.map (DerivedCategory.Plus.ι.preimage _) = _
  rw [Functor.map_preimage]
  simp [DerivedCategory.Plus.QCompιIso_hom_app,
    DerivedCategory.Plus.QCompιIso_inv_app]; rfl
private theorem supportHomNormalization_injective
    (N : SupportedHomCocycleNormalization J A hT j B rho)
    (I : CochainComplex.Plus (Sheaf J (ModuleCat.{u + 1} A)))
    [∀ n : ℤ, Injective (I.obj.X n)] (a : ℤ)
    (x : ((Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j).mapHomologicalComplex
      (ComplexShape.up ℤ) |>.obj I.obj).cycles a) :
    ∃ f : B ⟶ I.obj.X a,
      N.theta.hom.app (I.obj.X a) f =
        ((Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j).mapHomologicalComplex
          (ComplexShape.up ℤ) |>.obj I.obj).iCycles a x ∧
      ∃ hf : f ≫ I.obj.d a (a + 1) = 0,
        N.chi (DerivedCategory.Plus.Q.obj I) a
          ((Sheaf.supportSequenceModelIso J (ModuleCat.{u + 1} A)
            (Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j) I
            (DerivedCategory.Plus.Q.obj I) (Iso.refl _) a).hom
              (((Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j).mapHomologicalComplex
                (ComplexShape.up ℤ) |>.obj I.obj).homologyπ a x)) =
          supportedHomLocalizedCocycle I.obj a f hf := by
  obtain ⟨f, ⟨hf, hfn⟩, _⟩ := N.cocycle I I (𝟙 I) a x
  obtain ⟨hd, hchi⟩ := hfn
  refine ⟨f, hf, hd, ?_⟩
  rw [supportHomResolutionIso_id J I] at hchi
  have hqi : (DerivedCategory.Plus.QCompιIso
    (Sheaf J (ModuleCat.{u + 1} A))).inv.app I = 𝟙 _ := rfl
  rw [hqi] at hchi
  dsimp only [Iso.refl_inv] at hchi
  repeat first
    | erw [CategoryTheory.Functor.map_id] at hchi
    | erw [Category.comp_id] at hchi
  exact hchi
private theorem supportHomModelIso_refl_hom
    (I : CochainComplex.Plus (Sheaf J (ModuleCat.{u + 1} A)))
    [∀ n : ℤ, Injective (I.obj.X n)] (a : ℤ) :
    (Sheaf.supportSequenceModelIso J (ModuleCat.{u + 1} A)
      (Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j) I
      (DerivedCategory.Plus.Q.obj I) (Iso.refl _) a).hom =
    (DerivedCategory.Plus.homologyFunctorObjQIso
      ((Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j).mapCochainComplexPlus.obj I)
        a).inv ≫
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) a).map
        ((Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j).rightDerivedFunctorPlusUnith.app
          ((HomotopyCategory.Plus.quotient _).obj I)) := by
  have hs : (DerivedCategory.Plus.quotientCompQhIso (ModuleCat.{u + 1} A)).inv.app
      ((Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j).mapCochainComplexPlus.obj
        I) = 𝟙 _ := by
    apply DerivedCategory.Plus.ι.map_injective
    exact CategoryTheory.Quotient.lift.isLift_inv _ _ _ _
  have ht : (DerivedCategory.Plus.quotientCompQhIso
      (Sheaf J (ModuleCat.{u + 1} A))).hom.app I = 𝟙 _ := by
    apply DerivedCategory.Plus.ι.map_injective
    exact CategoryTheory.Quotient.lift.isLift_hom _ _ _ _
  simp only [Sheaf.supportSequenceModelIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.refl_hom, asIso_hom, Iso.app_hom, Iso.app_inv, hs, ht,
    Functor.quotientCompMapHomotopyCategoryPlusIso, Iso.refl_inv, NatTrans.id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  repeat first
    | erw [CategoryTheory.Functor.map_id]
    | erw [Category.id_comp]
    | erw [Category.comp_id]

end
private theorem supportHomExactCocycle_numerator
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {B : C} {B' : D} (g : B' ⟶ L.obj B)
    (I : CochainComplex C ℤ) (J : CochainComplex D ℤ)
    (t : (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ J)
    (a : ℤ) (f : B ⟶ I.X a) (hf : f ≫ I.d a (a + 1) = 0)
    (hgf : (g ≫ L.map f ≫ t.f a) ≫ J.d a (a + 1) = 0) :
    (DerivedCategory.singleFunctor D 0).map g ≫
      (L.mapDerivedCategorySingleFunctor 0).inv.app B ≫
      L.mapDerivedCategory.map
        (supportedHomLocalizedCocycle I a f hf) ≫
      (L.mapDerivedCategory.commShiftIso a).hom.app (DerivedCategory.Q.obj I) ≫
      ((L.mapDerivedCategoryFactors.hom.app I)⟦a⟧') ≫
      (DerivedCategory.Q.map t)⟦a⟧' =
    supportedHomLocalizedCocycle J a (g ≫ L.map f ≫ t.f a) hgf := by
  rw [supportedHomLocalizedCocycle_eq, supportedHomLocalizedCocycle_eq]
  have hsource : (L.mapDerivedCategorySingleFunctor 0).inv.app B ≫
      L.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor C 0).obj B) =
      DerivedCategory.Q.map ((L.mapCochainComplexSingleFunctor 0).inv.app B) := by
    simpa only [CochainComplex.singleFunctor] using!
      L.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app B
  have hnum : (CochainComplex.singleFunctor D 0).map g ≫
      (L.mapCochainComplexSingleFunctor 0).inv.app B ≫
      ShiftedHom.map (Cocycle.equivHomShift.symm
        (Cocycle.fromSingleMk f (zero_add a) (a + 1) rfl hf))
          (L.mapHomologicalComplex (.up ℤ)) ≫ t⟦a⟧' =
      Cocycle.equivHomShift.symm
        (Cocycle.fromSingleMk (g ≫ L.map f ≫ t.f a)
          (zero_add a) (a + 1) rfl hgf) := by
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
  have hn := ShiftedHom.map_naturality
    (Cocycle.equivHomShift.symm
      (Cocycle.fromSingleMk f (zero_add a) (a + 1) rfl hf))
    L.mapDerivedCategoryFactors.hom
  simp only [ShiftedHom.comp_map, ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp] at hn
  have hnat : L.mapDerivedCategory.map
      (ShiftedHom.map (Cocycle.equivHomShift.symm
        (Cocycle.fromSingleMk f (zero_add a) (a + 1) rfl hf)) DerivedCategory.Q) ≫
        (L.mapDerivedCategory.commShiftIso a).hom.app (DerivedCategory.Q.obj I) ≫
        (L.mapDerivedCategoryFactors.hom.app I)⟦a⟧' =
      L.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor C 0).obj B) ≫
        ShiftedHom.map (ShiftedHom.map (Cocycle.equivHomShift.symm
          (Cocycle.fromSingleMk f (zero_add a) (a + 1) rfl hf))
            (L.mapHomologicalComplex (ComplexShape.up ℤ))) DerivedCategory.Q := by
    simpa only [ShiftedHom.map, Category.assoc] using hn
  erw [reassoc_of% hnat, reassoc_of% hsource]
  have hnum' :
      (ShiftedHom.mk₀ 0 rfl ((singleFunctor D 0).map g ≫
        (L.mapCochainComplexSingleFunctor 0).inv.app B)).comp
        ((ShiftedHom.map (Cocycle.equivHomShift.symm
          (Cocycle.fromSingleMk f (zero_add a) (a + 1) rfl hf))
            (L.mapHomologicalComplex (.up ℤ))).comp
              (ShiftedHom.mk₀ 0 rfl t) (zero_add _)) (add_zero _) =
      Cocycle.equivHomShift.symm
        (Cocycle.fromSingleMk (g ≫ L.map f ≫ t.f a)
          (zero_add a) (a + 1) rfl hgf) := by
    simpa only [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀, Category.assoc] using hnum
  have hn' := congrArg (fun z ↦ ShiftedHom.map z DerivedCategory.Q) hnum'
  rw [ShiftedHom.map_comp, ShiftedHom.map_comp,
    ShiftedHom.map_mk₀, ShiftedHom.map_mk₀] at hn'
  simp only [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀,
    Functor.map_comp, Category.assoc] at hn'
  exact hn'

private theorem supportHomExactFactor_hom
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (I : CochainComplex.Plus C) :
    DerivedCategory.Plus.ι.map (L.mapDerivedCategoryPlusFactorsh.hom.app
      ((HomotopyCategory.Plus.quotient C).obj I)) =
      L.mapDerivedCategoryFactors.hom.app I.obj := by
  erw [Functor.ι_map_mapDerivedCategoryPlusFactorsh_hom_app,
    Functor.mapDerivedCategoryFactorsh_hom_app]
  have hq : (DerivedCategory.quotientCompQhIso C).hom.app I.obj = 𝟙 _ := rfl
  have hq' : (DerivedCategory.quotientCompQhIso D).inv.app
      ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj) = 𝟙 _ := rfl
  have hh : (L.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app I.obj = 𝟙 _ := rfl
  erw [hq, hq', hh]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  erw [Category.id_comp, Category.comp_id, Category.comp_id]
  rfl

private theorem supportHomEvaluation_naturality
    {A : Type (u + 1)} [CommRing A]
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J (ModuleCat.{u + 1} A)]
    [IsGrothendieckAbelian.{u + 1} (Sheaf J (ModuleCat.{u + 1} A))]
    {T W : C} (j : W ⟶ T) (B : Sheaf J (ModuleCat.{u + 1} A))
    (θ : SupportedHomEvaluationIso J A j B)
    {M N : Sheaf J (ModuleCat.{u + 1} A)} (g : M ⟶ N) (f : B ⟶ M) :
    θ.hom.app N (f ≫ g) =
      (Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j).map g
        (θ.hom.app M f) := by
  exact congrArg (fun k : AddCommGrpCat.of (B ⟶ M) ⟶
    AddCommGrpCat.of ((Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j).obj N) ↦
      k.hom f) (θ.hom.naturality g)

private theorem supportHom_transport_injective
    {A : Type (u + 1)} [CommRing A]
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (J' : GrothendieckTopology D)
    [HasSheafify J (ModuleCat.{u + 1} A)]
    [HasSheafify J' (ModuleCat.{u + 1} A)]
    [IsGrothendieckAbelian.{u + 1} (Sheaf J (ModuleCat.{u + 1} A))]
    [IsGrothendieckAbelian.{u + 1} (Sheaf J' (ModuleCat.{u + 1} A))]
    {T W : C} (hT : IsTerminal T) (j : W ⟶ T)
    {T' W' : D} (hT' : IsTerminal T') (j' : W' ⟶ T')
    (B : Sheaf J (ModuleCat.{u + 1} A)) (B' : Sheaf J' (ModuleCat.{u + 1} A))
    (rho : (constantSheaf J (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A) ⟶ B)
    (rho' : (constantSheaf J' (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A) ⟶ B')
    (N : SupportedHomCocycleNormalization J A hT j B rho)
    (N' : SupportedHomCocycleNormalization J' A hT' j' B' rho')
    (L : Sheaf J (ModuleCat.{u + 1} A) ⥤ Sheaf J' (ModuleCat.{u + 1} A))
    [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (d : L.obj B ≅ B')
    (tau : Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j ⟶
      L ⋙ Sheaf.supportedSectionsFunctor J' (ModuleCat.{u + 1} A) j')
    (heval : ∀ (M : Sheaf J (ModuleCat.{u + 1} A)) (f : B ⟶ M),
      N'.theta.hom.app (L.obj M) (d.inv ≫ L.map f) = tau.app M (N.theta.hom.app M f))
    (I : CochainComplex.Plus (Sheaf J (ModuleCat.{u + 1} A)))
    [∀ n : ℤ, Injective (I.obj.X n)] (a : ℤ)
    (x : (Sheaf.supportHypercohomologyFunctor J (ModuleCat.{u + 1} A) j a).obj
      (DerivedCategory.Plus.Q.obj I)) :
    let S := Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j
    let S' := Sheaf.supportedSectionsFunctor J' (ModuleCat.{u + 1} A) j'
    let b := Functor.normalizedSupportTransport L S S' tau
    N'.chi (L.mapDerivedCategoryPlus.obj (DerivedCategory.Plus.Q.obj I)) a
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) a).map
          (b.app (DerivedCategory.Plus.Q.obj I)) x) =
      (DerivedCategory.singleFunctor (Sheaf J' (ModuleCat.{u + 1} A)) 0).map d.inv ≫
        (L.mapDerivedCategorySingleFunctor 0).inv.app B ≫
        L.mapDerivedCategory.map (N.chi (DerivedCategory.Plus.Q.obj I) a x) ≫
        (L.mapDerivedCategory.commShiftIso a).hom.app (DerivedCategory.Plus.Q.obj I).obj := by
  let S := Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j
  let S' := Sheaf.supportedSectionsFunctor J' (ModuleCat.{u + 1} A) j'
  let H := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) a
  let M := L.mapCochainComplexPlus.obj I
  obtain ⟨m, hm⟩ := M.2
  have : M.obj.IsStrictlyGE m := hm
  obtain ⟨J₀, hj, e, he⟩ := CochainComplex.Plus.exists_quasiIso_injective M m
  let R := (InjectiveObject.ι (Sheaf J' (ModuleCat.{u + 1} A))).mapCochainComplexPlus.obj J₀
  have hi (n : ℤ) : Injective (R.obj.X n) := (J₀.obj.X n).2
  have : QuasiIso e.hom := he
  have : IsIso (DerivedCategory.Plus.Q.map e) :=
    Localization.inverts DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso _) _ he
  let c := Functor.normalizedSupportChainMap L S S' tau I R e.hom
  let EI := Sheaf.supportSequenceModelIso J (ModuleCat.{u + 1} A) S I
    (DerivedCategory.Plus.Q.obj I) (Iso.refl _) a
  obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective
    (((S.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj).homologyπ a)).mp
      inferInstance (EI.inv x)
  have hx : EI.hom
      (((S.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj).homologyπ a y) = x := by
    rw [hy]
    exact ConcreteCategory.congr_hom EI.inv_hom_id x
  obtain ⟨f, hf, hdf, hchi⟩ := supportHomNormalization_injective J hT j B rho N I a y
  let y' := HomologicalComplex.cyclesMap c.hom a y
  obtain ⟨f', hf', hdf', hchi'⟩ :=
    supportHomNormalization_injective J' hT' j' B' rho' N' R a y'
  have hfeq : f' = d.inv ≫ L.map f ≫ e.hom.f a := by
    apply (AddCommGrpCat.mono_iff_injective (N'.theta.hom.app (R.obj.X a))).mp inferInstance
    rw [hf']
    have hc := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i c.hom a) y
    simp only [ConcreteCategory.comp_apply] at hc
    change ((S'.mapHomologicalComplex (ComplexShape.up ℤ)).obj R.obj).iCycles a y' = _ at hc
    rw [hc]
    have hn := supportHomEvaluation_naturality J' j' B' N'.theta
      (e.hom.f a) (d.inv ≫ L.map f)
    erw [heval (I.obj.X a) f, hf] at hn
    erw [hn]
    have hh := ConcreteCategory.congr_hom
      (Functor.normalizedSupportChainMap_f L S S' tau I R e.hom a)
        (((S.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj).iCycles a y)
    exact hh.symm
  subst f'
  let ER := Sheaf.supportSequenceModelIso J' (ModuleCat.{u + 1} A) S' R
    (DerivedCategory.Plus.Q.obj R) (Iso.refl _) a
  let eD : L.mapDerivedCategoryPlus.obj (DerivedCategory.Plus.Q.obj I) ≅
      DerivedCategory.Plus.Q.obj R :=
    L.mapDerivedCategoryPlusFactorsh.app ((HomotopyCategory.Plus.quotient _).obj I) ≪≫
      asIso (DerivedCategory.Plus.Q.map e)
  have hmodel : EI.hom ≫ H.map
      ((Functor.normalizedSupportTransport L S S' tau).app (DerivedCategory.Plus.Q.obj I)) ≫
        H.map (S'.rightDerivedFunctorPlus.map eD.hom) =
      HomologicalComplex.homologyMap c.hom a ≫ ER.hom := by
    have hI := supportHomModelIso_refl_hom J j I a
    have hR := supportHomModelIso_refl_hom J' j' R a
    change EI.hom = _ at hI
    change ER.hom = _ at hR
    rw [hI, hR]
    exact Functor.normalizedSupportTransport_homology_comp
      L S S' tau I R e a
  have hclass : H.map (S'.rightDerivedFunctorPlus.map eD.hom)
      (H.map ((Functor.normalizedSupportTransport L S S' tau).app
        (DerivedCategory.Plus.Q.obj I)) x) =
        ER.hom (((S'.mapHomologicalComplex (ComplexShape.up ℤ)).obj R.obj).homologyπ a y') := by
    have h := ConcreteCategory.congr_hom hmodel
      (((S.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj).homologyπ a y)
    simp only [ConcreteCategory.comp_apply, hx] at h
    erw [h]
    congr 1
    exact ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality c.hom a) y
  have heD : DerivedCategory.Plus.ι.map eD.hom =
      L.mapDerivedCategoryFactors.hom.app I.obj ≫ DerivedCategory.Q.map e.hom := by
    dsimp only [eD, Iso.trans_hom, asIso_hom]
    erw [CategoryTheory.Functor.map_comp,
      supportHomExactFactor_hom.{u + 2, u + 2, u + 1, u + 1, u + 1, u + 1}]
    rfl
  apply (cancel_mono ((DerivedCategory.Plus.ι.map eD.hom)⟦a⟧')).mp
  rw [← N'.naturality _ _ eD.hom a]
  change N'.chi _ a (H.map (S'.rightDerivedFunctorPlus.map eD.hom)
      (H.map ((Functor.normalizedSupportTransport L S S' tau).app _) x)) = _
  rw [hclass, hchi']
  have hs : N.chi (DerivedCategory.Plus.Q.obj I) a x =
      supportedHomLocalizedCocycle I.obj a f hdf := by
    rw [← hx]
    exact hchi
  rw [hs, heD, CategoryTheory.Functor.map_comp]
  simpa only [Category.assoc] using!
    (supportHomExactCocycle_numerator.{u + 2, u + 2, u + 1, u + 1, u + 1, u + 1}
      L d.inv I.obj R.obj e.hom a f hdf hdf').symm

/-- The module-valued compatibility formula, with its derived support map supplied. -/
def moduleSupportedHomCompatible
    {A : Type (u + 1)} [CommRing A]
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (J' : GrothendieckTopology D)
    [HasSheafify J (ModuleCat.{u + 1} A)]
    [HasSheafify J' (ModuleCat.{u + 1} A)]
    [IsGrothendieckAbelian.{u + 1} (Sheaf J (ModuleCat.{u + 1} A))]
    [IsGrothendieckAbelian.{u + 1} (Sheaf J' (ModuleCat.{u + 1} A))]
    {T W : C} (j : W ⟶ T) {T' W' : D} (j' : W' ⟶ T')
    (B : Sheaf J (ModuleCat.{u + 1} A)) (B' : Sheaf J' (ModuleCat.{u + 1} A))
    (chi : SupportedHomChi J A j B) (chi' : SupportedHomChi J' A j' B')
    (L : Sheaf J (ModuleCat.{u + 1} A) ⥤ Sheaf J' (ModuleCat.{u + 1} A))
    [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (d : L.obj B ≅ B')
    (b : (Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j).rightDerivedFunctorPlus ⟶
      L.mapDerivedCategoryPlus ⋙
        (Sheaf.supportedSectionsFunctor J' (ModuleCat.{u + 1} A) j').rightDerivedFunctorPlus)
    (K : DerivedCategory.Plus (Sheaf J (ModuleCat.{u + 1} A))) (a : ℤ) : Prop :=
  ∀ x : (Sheaf.supportHypercohomologyFunctor J (ModuleCat.{u + 1} A) j a).obj K,
    chi' (L.mapDerivedCategoryPlus.obj K) a
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) a).map (b.app K) x) =
      Functor.representableTransportHom L d K a (chi K a x)

/-- Exact inverse image transports a module-valued, cocycle-normalized supported-Hom
comparison. -/
theorem moduleSupportedHom_transport
    {A : Type (u + 1)} [CommRing A]
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (J' : GrothendieckTopology D)
    [HasSheafify J (ModuleCat.{u + 1} A)]
    [HasSheafify J' (ModuleCat.{u + 1} A)]
    [IsGrothendieckAbelian.{u + 1} (Sheaf J (ModuleCat.{u + 1} A))]
    [IsGrothendieckAbelian.{u + 1} (Sheaf J' (ModuleCat.{u + 1} A))]
    {T W : C} (hT : IsTerminal T) (j : W ⟶ T)
    {T' W' : D} (hT' : IsTerminal T') (j' : W' ⟶ T')
    (B : Sheaf J (ModuleCat.{u + 1} A)) (B' : Sheaf J' (ModuleCat.{u + 1} A))
    (rho : (constantSheaf J (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A) ⟶ B)
    (rho' : (constantSheaf J' (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A) ⟶ B')
    (N : SupportedHomCocycleNormalization J A hT j B rho)
    (N' : SupportedHomCocycleNormalization J' A hT' j' B' rho')
    (L : Sheaf J (ModuleCat.{u + 1} A) ⥤ Sheaf J' (ModuleCat.{u + 1} A))
    [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (d : L.obj B ≅ B')
    (tau : Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j ⟶
      L ⋙ Sheaf.supportedSectionsFunctor J' (ModuleCat.{u + 1} A) j')
    (heval : ∀ (M : Sheaf J (ModuleCat.{u + 1} A)) (f : B ⟶ M),
      N'.theta.hom.app (L.obj M) (d.inv ≫ L.map f) = tau.app M (N.theta.hom.app M f))
    (K : DerivedCategory.Plus (Sheaf J (ModuleCat.{u + 1} A))) (a : ℤ) :
    let S := Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j
    let S' := Sheaf.supportedSectionsFunctor J' (ModuleCat.{u + 1} A) j'
    let b : S.rightDerivedFunctorPlus ⟶ L.mapDerivedCategoryPlus ⋙ S'.rightDerivedFunctorPlus :=
      (Functor.rightUnitor _).inv ≫
        (Functor.isoWhiskerLeft _
          (Functor.mapDerivedCategoryPlusIdIso (ModuleCat.{u + 1} A))).inv ≫
        Functor.rightDerivedFunctorPlusBaseChange
          (G := S) (G' := S') (β := L) (γ := 𝟭 (ModuleCat.{u + 1} A))
          ((Functor.rightUnitor _).hom ≫ tau)
    moduleSupportedHomCompatible J J' j j' B B' N.chi N'.chi L d b K a := by
  dsimp only
  intro x
  unfold Functor.representableTransportHom
  rw [← Functor.normalizedSupportTransport_eq L
    (Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j)
    (Sheaf.supportedSectionsFunctor J' (ModuleCat.{u + 1} A) j') tau]
  let S := Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j
  let S' := Sheaf.supportedSectionsFunctor J' (ModuleCat.{u + 1} A) j'
  let H := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) a
  let b := Functor.normalizedSupportTransport L S S' tau
  obtain ⟨m, hm⟩ := K.2
  have : K.IsGE m := (K.isGE_ι_obj_iff m).mp hm
  obtain ⟨J₀, _, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso K m
  let I := (InjectiveObject.ι (Sheaf J (ModuleCat.{u + 1} A))).mapCochainComplexPlus.obj J₀
  have hi (n : ℤ) : Injective (I.obj.X n) := (J₀.obj.X n).2
  have hh := supportHom_transport_injective J J' hT j hT' j' B B' rho rho'
    N N' L d tau heval I a ((S.rightDerivedFunctorPlus ⋙ H).map e.inv x)
  have hb := congrArg H.map (b.naturality e.inv)
  simp only [Functor.comp_map, CategoryTheory.Functor.map_comp] at hb
  have hb' := ConcreteCategory.congr_hom hb x
  simp only [ConcreteCategory.comp_apply] at hb'
  have hleft : N'.chi (L.mapDerivedCategoryPlus.obj (DerivedCategory.Plus.Q.obj I)) a
      (H.map (b.app (DerivedCategory.Plus.Q.obj I))
        ((S.rightDerivedFunctorPlus ⋙ H).map e.inv x)) =
      N'.chi (L.mapDerivedCategoryPlus.obj K) a (H.map (b.app K) x) ≫
        (DerivedCategory.Plus.ι.map (L.mapDerivedCategoryPlus.map e.inv))⟦a⟧' := by
    erw [hb']
    exact N'.naturality _ _ (L.mapDerivedCategoryPlus.map e.inv) a _
  change N'.chi _ a (H.map (b.app _) _) = _ at hh
  rw [hleft, N.naturality] at hh
  erw [L.mapDerivedCategory.map_comp] at hh
  have hn := (L.mapDerivedCategory.commShiftIso a).hom.naturality
    (DerivedCategory.Plus.ι.map e.inv)
  simp only [Functor.comp_map] at hn
  simp only [Category.assoc] at hh
  erw [hn] at hh
  apply (cancel_mono ((DerivedCategory.Plus.ι.map
    (L.mapDerivedCategoryPlus.map e.inv))⟦a⟧')).mp
  change _ ≫ _ = _ ≫ _ ≫ _ ≫ _ ≫ _ at hh
  with_unfolding_all
    simpa only [Functor.mapDerivedCategoryPlus, ObjectProperty.lift_map,
      ObjectProperty.homMk_hom, ObjectProperty.ι_map, ObjectProperty.ι_obj,
      ObjectProperty.lift_obj_obj,
      Functor.comp_map, Category.assoc] using! hh

end AlgebraicGeometry
