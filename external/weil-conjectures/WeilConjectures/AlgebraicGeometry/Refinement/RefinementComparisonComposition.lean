/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Refinement.RefinementComparisonIsomorphism

/-!
# Composition of the specified objectwise refinement comparison
-/

@[expose] public noncomputable section

set_option autoImplicit false
open CategoryTheory CategoryTheory.Abelian
namespace CategoryTheory.Functor
variable {C D E E' : Type*} [Category C] [Category D] [Category E] [Category E']
  [Abelian C] [Abelian D] [Abelian E] [Abelian E']
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [HasDerivedCategory E'] [HasKInjectiveResolutions C] [HasKInjectiveResolutions D]
  [HasKInjectiveResolutions E] [HasKInjectiveResolutions E']
omit [HasKInjectiveResolutions E] in
private theorem comp_unit_app (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    (K : HomotopyCategory C (.up ℤ)) :
    (rightDerivedFunctorCompUnit F G).app K =
      G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj K) ≫
        G.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app K) := by
  simp only [rightDerivedFunctorCompUnit, NatTrans.comp_app, whiskerLeft_app,
    whiskerRight_app, associator_hom_app, associator_inv_app, Category.id_comp]
  have hi : (mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app K = 𝟙 _ := by
    apply (cancel_epi ((mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app K)).mp
    rw [Iso.hom_inv_id_app, mapHomotopyCategoryCompIso_refl_hom_app, Category.comp_id]
  rw [hi, DerivedCategory.Qh.map_id]
  erw [Category.id_comp, Category.comp_id]

omit [HasKInjectiveResolutions E] in
private theorem comp_fac (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive] [F.PreservesKInjectiveComplexes]
    (e : F ⋙ G ≅ H) (K : HomotopyCategory C (.up ℤ)) :
    (rightDerivedFunctorCompUnit F G).app K ≫
        (rightDerivedFunctorCompIso' F G e).hom.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app K) ≫
        H.rightDerivedFunctorUnit.app K := by
  simp [rightDerivedFunctorCompIso', rightDerivedFunctorCompIso,
    rightDerivedFunctorNatIso, rightDerivedFunctorNatTrans]

omit [HasKInjectiveResolutions D] in
private theorem natTrans_fac {F G : C ⥤ D} [F.Additive] [G.Additive]
    (a : F ⟶ G) (K : HomotopyCategory C (.up ℤ)) :
    F.rightDerivedFunctorUnit.app K ≫
        (rightDerivedFunctorNatTrans a).app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory a (.up ℤ)).app K) ≫
        G.rightDerivedFunctorUnit.app K := by
  simp [rightDerivedFunctorNatTrans]

omit [HasKInjectiveResolutions E'] in
private theorem comp_assoc
    (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ E') (FG : C ⥤ E) (GH : D ⥤ E')
    (FGH : C ⥤ E')
    [F.Additive] [G.Additive] [H.Additive] [FG.Additive] [GH.Additive] [FGH.Additive]
    [F.PreservesKInjectiveComplexes] [G.PreservesKInjectiveComplexes]
    [FG.PreservesKInjectiveComplexes] [(F ⋙ G).PreservesKInjectiveComplexes]
    (e₁ : F ⋙ G ≅ FG) (e₂ : G ⋙ H ≅ GH) (e₃ : FG ⋙ H ≅ FGH) (e₄ : F ⋙ GH ≅ FGH)
    (hcompat : whiskerRight e₁.hom H ≫ e₃.hom = whiskerLeft F e₂.hom ≫ e₄.hom) :
    whiskerRight (rightDerivedFunctorCompIso' F G e₁).hom H.rightDerivedFunctor ≫
        (rightDerivedFunctorCompIso' FG H e₃).hom =
      whiskerLeft F.rightDerivedFunctor (rightDerivedFunctorCompIso' G H e₂).hom ≫
        (rightDerivedFunctorCompIso' F GH e₄).hom := by
  rw [← cancel_epi (whiskerRight (rightDerivedFunctorCompIso F G).hom
    H.rightDerivedFunctor)]
  refine rightDerived_ext ((F ⋙ G).rightDerivedFunctor ⋙ H.rightDerivedFunctor)
    (rightDerivedFunctorCompUnit (F ⋙ G) H) (HomotopyCategory.quasiIso C (.up ℤ)) _ _ _ ?_
  ext K : 2
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, comp_obj]
  have hCI₁ : (rightDerivedFunctorCompIso F G).hom.app (DerivedCategory.Qh.obj K) ≫
      (rightDerivedFunctorCompIso' F G e₁).hom.app (DerivedCategory.Qh.obj K) =
      (rightDerivedFunctorNatTrans e₁.hom).app (DerivedCategory.Qh.obj K) := by
    change _ ≫ ((rightDerivedFunctorCompIso F G).inv.app _ ≫ _) = _
    rw [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
    rfl
  have hfac₃ := comp_fac FG H FGH e₃ K
  have hfac₂ := comp_fac G H GH e₂ ((F.mapHomotopyCategory (.up ℤ)).obj K)
  have hfac₄ := comp_fac F GH FGH e₄ K
  trans DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory
      (whiskerRight e₁.hom H ≫ e₃.hom) (.up ℤ)).app K) ≫
    FGH.rightDerivedFunctorUnit.app K
  · have hn := H.rightDerivedFunctorUnit.naturality
      ((NatTrans.mapHomotopyCategory e₁.hom (.up ℤ)).app K)
    simp only [comp_obj, comp_map] at hn
    have hb : (H.mapHomotopyCategory (.up ℤ)).map
        ((NatTrans.mapHomotopyCategory e₁.hom (.up ℤ)).app K) =
        (NatTrans.mapHomotopyCategory (whiskerRight e₁.hom H) (.up ℤ)).app K := rfl
    rw [← Functor.map_comp_assoc, hCI₁, comp_unit_app, Category.assoc,
      ← Functor.map_comp_assoc, natTrans_fac, Functor.map_comp,
      Category.assoc, ← reassoc_of% hn]
    rw [← reassoc_of% (comp_unit_app FG H K), hfac₃, hb,
      ← Functor.map_comp_assoc, ← NatTrans.comp_app,
      ← NatTrans.mapHomotopyCategory_comp]
  · rw [hcompat]
    have hn := (rightDerivedFunctorCompIso' G H e₂).hom.naturality
      (F.rightDerivedFunctorUnit.app K)
    simp only [comp_obj, comp_map] at hn
    have hb : (NatTrans.mapHomotopyCategory e₂.hom (.up ℤ)).app
        ((F.mapHomotopyCategory (.up ℤ)).obj K) =
        (NatTrans.mapHomotopyCategory (whiskerLeft F e₂.hom) (.up ℤ)).app K := rfl
    have hc : (F ⋙ G).rightDerivedFunctorUnit.app K ≫
        (rightDerivedFunctorCompIso F G).hom.app (DerivedCategory.Qh.obj K) =
      (rightDerivedFunctorCompUnit F G).app K := by
      simp [rightDerivedFunctorCompIso]
    rw [comp_unit_app, Category.assoc, ← Functor.map_comp_assoc, hc, comp_unit_app,
      Functor.map_comp]
    simp only [Category.assoc]
    erw [← reassoc_of% (comp_unit_app G H ((F.mapHomotopyCategory (.up ℤ)).obj K)),
      reassoc_of% hn, reassoc_of% hfac₂]
    rw [← reassoc_of% (comp_unit_app F GH K), hfac₄, hb,
      ← Functor.map_comp_assoc, ← NatTrans.comp_app,
      ← NatTrans.mapHomotopyCategory_comp]

end CategoryTheory.Functor

namespace CategoryTheory.Functor
open CategoryTheory.Abelian
variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [HasKInjectiveResolutions C] [HasKInjectiveResolutions D]
  [HasKInjectiveResolutions E] [EnoughInjectives C] [EnoughInjectives D]

omit [HasKInjectiveResolutions D] [EnoughInjectives D] in
private theorem compat_fac (F : C ⥤ D) [F.Additive] (K : HomotopyCategory.Plus C) :
    DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnith.app K) ≫
        F.rightDerivedFunctorPlusCompatibility.hom.app (DerivedCategory.Plus.Qh.obj K) =
      F.rightDerivedFunctorUnit.app K.obj := by
  change F.rightDerivedFunctorPlusιUnit.app K ≫
    ((F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).rightDerivedNatTrans
      (DerivedCategory.Plus.ι ⋙ F.rightDerivedFunctor) F.rightDerivedFunctorPlusιUnit
      F.ιRightDerivedFunctorUnit (HomotopyCategory.Plus.quasiIso C) (𝟙 _)).app _ = _
  rw [rightDerivedNatTrans_app]
  exact Category.id_comp _

omit [HasKInjectiveResolutions E] in
private theorem comp_compat (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [F.PreservesInjectiveObjects]
    [F.PreservesKInjectiveComplexes] :
    whiskerRight (rightDerivedFunctorPlusCompIso F G).hom DerivedCategory.Plus.ι ≫
        whiskerLeft F.rightDerivedFunctorPlus G.rightDerivedFunctorPlusCompatibility.hom ≫
        whiskerRight F.rightDerivedFunctorPlusCompatibility.hom G.rightDerivedFunctor =
      (F ⋙ G).rightDerivedFunctorPlusCompatibility.hom ≫
        whiskerLeft DerivedCategory.Plus.ι (rightDerivedFunctorCompIso F G).hom := by
  refine rightDerived_ext ((F ⋙ G).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι)
    (F ⋙ G).rightDerivedFunctorPlusιUnit (HomotopyCategory.Plus.quasiIso C) _ _ _ ?_
  ext K : 2
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, comp_obj,
    rightDerivedFunctorPlusιUnit]
  have hc : (F ⋙ G).rightDerivedFunctorUnit.app K.obj ≫
      (rightDerivedFunctorCompIso F G).hom.app (DerivedCategory.Qh.obj K.obj) =
        (rightDerivedFunctorCompUnit F G).app K.obj := by
    simp [rightDerivedFunctorCompIso]
  rw [reassoc_of% (compat_fac (F ⋙ G) K)]
  erw [hc]
  rw [comp_unit_app]
  rw [← DerivedCategory.Plus.ι.map_comp_assoc, rightDerivedFunctorPlusCompIso_fac_app,
    rightDerivedFunctorPlusCompUnit_app, DerivedCategory.Plus.ι.map_comp]
  have hn := G.rightDerivedFunctorPlusCompatibility.hom.naturality
    (F.rightDerivedFunctorPlusUnith.app K)
  simp only [comp_map] at hn
  rw [Category.assoc, reassoc_of% hn, ← Category.assoc,
    compat_fac G (F.mapHomotopyCategoryPlus.obj K)]
  erw [← G.rightDerivedFunctor.map_comp, compat_fac F K]
  rfl

omit [HasKInjectiveResolutions E] in
private theorem natTrans_compat (F H : C ⥤ E) [F.Additive] [H.Additive] (τ : F ⟶ H) :
    whiskerRight (rightDerivedFunctorPlusNatTrans τ) DerivedCategory.Plus.ι ≫
        H.rightDerivedFunctorPlusCompatibility.hom =
      F.rightDerivedFunctorPlusCompatibility.hom ≫
        whiskerLeft DerivedCategory.Plus.ι (rightDerivedFunctorNatTrans τ) := by
  refine rightDerived_ext (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι)
    F.rightDerivedFunctorPlusιUnit (HomotopyCategory.Plus.quasiIso C) _ _ _ ?_
  ext K : 2
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, comp_obj,
    rightDerivedFunctorPlusιUnit]
  rw [← DerivedCategory.Plus.ι.map_comp_assoc, rightDerivedFunctorPlusNatTrans_app,
    DerivedCategory.Plus.ι.map_comp, Category.assoc, compat_fac H K,
    reassoc_of% (compat_fac F K)]
  erw [natTrans_fac]
  rfl

omit [HasKInjectiveResolutions E] in
private theorem comp'_compat (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive] [F.PreservesInjectiveObjects]
    [F.PreservesKInjectiveComplexes] (e : F ⋙ G ≅ H) (K : DerivedCategory.Plus C) :
    DerivedCategory.Plus.ι.map ((rightDerivedFunctorPlusCompIso' F G e).hom.app K) ≫
        H.rightDerivedFunctorPlusCompatibility.hom.app K =
      G.rightDerivedFunctorPlusCompatibility.hom.app (F.rightDerivedFunctorPlus.obj K) ≫
        G.rightDerivedFunctor.map (F.rightDerivedFunctorPlusCompatibility.hom.app K) ≫
          (rightDerivedFunctorCompIso' F G e).hom.app K.obj := by
  have hc := congr_app (comp_compat F G) K
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app] at hc
  have hn := congr_app (natTrans_compat (F ⋙ G) H e.hom) K
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app] at hn
  apply (cancel_epi (DerivedCategory.Plus.ι.map
    ((rightDerivedFunctorPlusCompIso F G).hom.app K))).mp
  dsimp only [rightDerivedFunctorPlusCompIso', rightDerivedFunctorCompIso',
    Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, rightDerivedFunctorPlusNatIso,
    rightDerivedFunctorNatIso]
  rw [DerivedCategory.Plus.ι.map_comp]
  simp only [← Category.assoc, ← DerivedCategory.Plus.ι.map_comp,
    Iso.hom_inv_id_app, Category.id_comp]
  simp only [Category.assoc]
  erw [reassoc_of% hc]
  change _ = (F ⋙ G).rightDerivedFunctorPlusCompatibility.hom.app K ≫
    (rightDerivedFunctorCompIso F G).hom.app K.obj ≫
    (rightDerivedFunctorCompIso F G).inv.app K.obj ≫
    (rightDerivedFunctorNatTrans e.hom).app K.obj
  rw [Iso.hom_inv_id_app_assoc]
  exact hn

end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale
universe u
open CategoryTheory

private theorem directImage_comp_compat
    (Λ : Type (u + 1)) [CommRing Λ]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (L : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))) :
    DerivedCategory.Plus.ι.map
        ((proEtaleComparisonDirectImageCompIso Λ f g).hom.app L) ≫
        (lowerStar (ModuleCat.{u + 1} Λ) (f ≫ g)).rightDerivedFunctorPlusCompatibility.hom.app L =
      (lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctorPlusCompatibility.hom.app
          ((lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus.obj L) ≫
        (lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctor.map
          ((lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlusCompatibility.hom.app L) ≫
        (finiteDirectImageComposition Λ f g).inv.app L.obj := by
  let A := ModuleCat.{u + 1} Λ
  let := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (upperStarLowerStarAdjunction A f)
  let := (upperStarLowerStarAdjunction A f).preservesKInjectiveComplexes
  exact CategoryTheory.Functor.comp'_compat (lowerStar A f) (lowerStar A g)
    (lowerStar A (f ≫ g)) (lowerStarComp A f g) L

end AlgebraicGeometry.ProEtale

private theorem transported_comp
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category* C₀] [Category* C₁] [Category* C₂]
    [Category* D₀] [Category* D₁] [Category* D₂]
    (I₀ : C₀ ⥤ D₀) (I₁ : C₁ ⥤ D₁) (I₂ : C₂ ⥤ D₂)
    (Rplus : C₀ ⥤ C₁) (Splus : C₁ ⥤ C₂) (RSplus : C₀ ⥤ C₂)
    (R : D₀ ⥤ D₁) (S : D₁ ⥤ D₂) (RS : D₀ ⥤ D₂)
    (tR : Rplus ⋙ I₁ ≅ I₀ ⋙ R) (tS : Splus ⋙ I₂ ≅ I₁ ⋙ S)
    (tRS : RSplus ⋙ I₂ ≅ I₀ ⋙ RS)
    (cplus : Rplus ⋙ Splus ≅ RSplus) (c : R ⋙ S ≅ RS)
    (hcompat : ∀ A, I₂.map (cplus.hom.app A) ≫ tRS.hom.app A =
      tS.hom.app (Rplus.obj A) ≫ S.map (tR.hom.app A) ≫ c.hom.app (I₀.obj A))
    {A : C₀} {B : C₁} {C : C₂} {A' : D₀} {B' : D₁} {C' : D₂}
    (qA : I₀.obj A ≅ A') (qB : I₁.obj B ≅ B') (qC : I₂.obj C ≅ C')
    (a : B ≅ Rplus.obj A) (b : C ≅ Splus.obj B) :
    (qC.symm ≪≫ I₂.mapIso b ≪≫ tS.app B ≪≫ S.mapIso qB) ≪≫
        S.mapIso (qB.symm ≪≫ I₁.mapIso a ≪≫ tR.app A ≪≫ R.mapIso qA) ≪≫
        c.app A' =
      qC.symm ≪≫ I₂.mapIso (b ≪≫ Splus.mapIso a ≪≫ cplus.app A) ≪≫
        tRS.app A ≪≫ RS.mapIso qA := by
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom,
    Functor.map_comp, Category.assoc]
  rw [← S.map_comp_assoc, qB.hom_inv_id, S.map_id, Category.id_comp]
  have hn := tS.hom.naturality a.hom
  simp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  have hc := c.hom.naturality qA.hom
  simp only [Functor.comp_map] at hc
  rw [hc, ← reassoc_of% (hcompat A)]

namespace AlgebraicGeometry.ProEtale
universe u
open CategoryTheory
private theorem properOpen_ambient_comp
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {T₁ T₂ T₃ X : Scheme.{u}} [IsNoetherian T₁] [IsNoetherian T₂] [IsNoetherian T₃]
    (r : T₁ ⟶ T₂) (s : T₂ ⟶ T₃) [IsProper r] [IsProper s]
    (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) (j₃ : X ⟶ T₃)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] [IsOpenImmersion j₃]
    (hr : j₁ ≫ r = j₂) (hs : j₂ ≫ s = j₃)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    properOpenProEtaleIso Λ (r ≫ s) j₁ j₃
        ((Category.assoc j₁ r s).symm.trans ((congrArg (· ≫ s) hr).trans hs)) L =
      properOpenProEtaleIso Λ s j₂ j₃ hs L ≪≫
        (lowerStar (ModuleCat.{u + 1} Λ) s).rightDerivedFunctor.mapIso
          (properOpenProEtaleIso Λ r j₁ j₂ hr L) ≪≫
        (finiteDirectImageComposition Λ r s).symm.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₁).mapDerivedCategory.obj
            ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj L.obj)) := by
  let A := ModuleCat.{u + 1} Λ
  let N := comparisonUpperStar A X
  let L₀ := N.mapDerivedCategoryPlus.obj L
  let q (T : Scheme.{u}) (j : X ⟶ T) [IsOpenImmersion j] :=
    ((openImmersionLowerShriek A j).mapDerivedCategoryPlusCompatibility.app L₀) ≪≫
      (openImmersionLowerShriek A j).mapDerivedCategory.mapIso
        (N.mapDerivedCategoryPlusCompatibility.app L)
  have hc : properOpenProEtaleIsoPlus Λ (r ≫ s) j₁ j₃
      ((Category.assoc j₁ r s).symm.trans ((congrArg (· ≫ s) hr).trans hs)) L =
      properOpenProEtaleIsoPlus Λ s j₂ j₃ hs L ≪≫
        (lowerStar A s).rightDerivedFunctorPlus.mapIso
          (properOpenProEtaleIsoPlus Λ r j₁ j₂ hr L) ≪≫
        (proEtaleComparisonDirectImageCompIso Λ r s).app
          ((openImmersionLowerShriek A j₁).mapDerivedCategoryPlus.obj L₀) := by
    apply Iso.ext
    exact properOpenProEtaleIsoPlus_comp Λ r s j₁ j₂ j₃ hr hs L
  have ht := transported_comp
    DerivedCategory.Plus.ι DerivedCategory.Plus.ι DerivedCategory.Plus.ι
    (lowerStar A r).rightDerivedFunctorPlus (lowerStar A s).rightDerivedFunctorPlus
    (lowerStar A (r ≫ s)).rightDerivedFunctorPlus
    (lowerStar A r).rightDerivedFunctor (lowerStar A s).rightDerivedFunctor
    (lowerStar A (r ≫ s)).rightDerivedFunctor
    (lowerStar A r).rightDerivedFunctorPlusCompatibility
    (lowerStar A s).rightDerivedFunctorPlusCompatibility
    (lowerStar A (r ≫ s)).rightDerivedFunctorPlusCompatibility
    (proEtaleComparisonDirectImageCompIso Λ r s)
    (finiteDirectImageComposition Λ r s).symm
    (directImage_comp_compat Λ r s)
    (q T₁ j₁) (q T₂ j₂) (q T₃ j₃)
    (properOpenProEtaleIsoPlus Λ r j₁ j₂ hr L)
    (properOpenProEtaleIsoPlus Λ s j₂ j₃ hs L)
  rw [← hc] at ht
  simpa [q, properOpenProEtaleIso, Functor.mapIso_trans, Iso.trans_assoc, N, A, L₀]
    using ht.symm
end AlgebraicGeometry.ProEtale

private theorem conjugated_comp
    {C₀ C₁ C₂ : Type*} [Category* C₀] [Category* C₁] [Category* C₂]
    (R : C₀ ⥤ C₁) (S : C₁ ⥤ C₂) (RS : C₀ ⥤ C₂) (c : R ⋙ S ≅ RS)
    {A A' : C₀} {B B' : C₁} {C C' : C₂}
    (qA : A ≅ A') (qB : B ≅ B') (qC : C ≅ C')
    (a : B ≅ R.obj A) (b : C ≅ S.obj B) :
    (qC.symm ≪≫ b ≪≫ S.mapIso qB) ≪≫
        S.mapIso (qB.symm ≪≫ a ≪≫ R.mapIso qA) ≪≫ c.app A' =
      qC.symm ≪≫ (b ≪≫ S.mapIso a ≪≫ c.app A) ≪≫ RS.mapIso qA := by
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom,
    Functor.map_comp, Category.assoc]
  rw [← S.map_comp_assoc, qB.hom_inv_id, S.map_id, Category.id_comp]
  have hc := c.hom.naturality qA.hom
  simp only [Functor.comp_map] at hc
  rw [hc]

namespace AlgebraicGeometry.ProEtale
universe u
open CategoryTheory
private def factorizationIso (Λ : Type (u + 1)) [CommRing Λ]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (e : f ≫ g = h) :
    (lowerStar (ModuleCat.{u + 1} Λ) h).rightDerivedFunctor ≅
      (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor ⋙
        (lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctor :=
  eqToIso (congrArg (fun q ↦ (lowerStar (ModuleCat.{u + 1} Λ) q).rightDerivedFunctor)
      e.symm) ≪≫ finiteDirectImageComposition Λ f g

private theorem derived_comp_congr (Λ : Type (u + 1)) [CommRing Λ]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (e : f ≫ g = h) :
    (let := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).preservesKInjectiveComplexes
     Functor.rightDerivedFunctorCompIso'
      (lowerStar (ModuleCat.{u + 1} Λ) f) (lowerStar (ModuleCat.{u + 1} Λ) g)
      (lowerStarComp (ModuleCat.{u + 1} Λ) f g ≪≫
        lowerStarCongr (ModuleCat.{u + 1} Λ) e)).symm =
      factorizationIso Λ f g h e := by
  subst h
  simp [lowerStarCongr, factorizationIso, finiteDirectImageComposition]

private theorem finiteDirectImage_assoc (Λ : Type (u + 1)) [CommRing Λ]
    {X Y Z W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) :
    finiteDirectImageComposition Λ f (g ≫ h) ≪≫
        Functor.isoWhiskerLeft (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor
          (finiteDirectImageComposition Λ g h) =
      factorizationIso Λ (f ≫ g) h (f ≫ g ≫ h) (Category.assoc f g h) ≪≫
        Functor.isoWhiskerRight (finiteDirectImageComposition Λ f g)
          (lowerStar (ModuleCat.{u + 1} Λ) h).rightDerivedFunctor ≪≫
        Functor.associator _ _ _ := by
  let A := ModuleCat.{u + 1} Λ
  let F := lowerStar A f
  let G := lowerStar A g
  let H := lowerStar A h
  let FG := lowerStar A (f ≫ g)
  let GH := lowerStar A (g ≫ h)
  let FGH := lowerStar A (f ≫ g ≫ h)
  let := (upperStarLowerStarAdjunction A f).preservesKInjectiveComplexes
  let := (upperStarLowerStarAdjunction A g).preservesKInjectiveComplexes
  let := (upperStarLowerStarAdjunction A (f ≫ g)).preservesKInjectiveComplexes
  let : (F ⋙ G).PreservesKInjectiveComplexes :=
    (upperStarLowerStarAdjunction A g |>.comp
      (upperStarLowerStarAdjunction A f)).preservesKInjectiveComplexes
  let e₁ := lowerStarComp A f g
  let e₂ := lowerStarComp A g h
  let e₃ := lowerStarComp A (f ≫ g) h ≪≫ lowerStarCongr A (Category.assoc f g h)
  let e₄ := lowerStarComp A f (g ≫ h)
  have hcompat : Functor.whiskerRight e₁.hom H ≫ e₃.hom =
      Functor.whiskerLeft F e₂.hom ≫ e₄.hom := by
    apply NatTrans.ext
    funext M
    have hc := congr_app (congrArg Iso.hom (legacy_lowerStarComp_assoc A f g h)) M
    simpa [e₁, e₂, e₃, e₄, H, F, Iso.trans_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom] using hc.symm
  have hc := CategoryTheory.Functor.comp_assoc F G H FG GH FGH e₁ e₂ e₃ e₄ hcompat
  have hd := derived_comp_congr Λ (f ≫ g) h (f ≫ g ≫ h) (Category.assoc f g h)
  apply Iso.ext_inv
  simp only [Iso.trans_inv, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv]
  rw [← hd]
  apply NatTrans.ext
  funext K
  have hk := congr_app hc K
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp, finiteDirectImageComposition,
    Iso.symm_inv] using hk.symm

end AlgebraicGeometry.ProEtale

private theorem comparison_comp
    {C₁ C₂ C₃ D : Type*} [Category* C₁] [Category* C₂] [Category* C₃] [Category* D]
    (R : C₁ ⥤ C₂) (S : C₂ ⥤ C₃) (RS : C₁ ⥤ C₃)
    (P₁ : C₁ ⥤ D) (P₂ : C₂ ⥤ D) (P₃ : C₃ ⥤ D)
    (c : RS ≅ R ⋙ S) (d₁ : P₁ ≅ R ⋙ P₂) (d₂ : P₂ ≅ S ⋙ P₃)
    (d₃ : P₁ ≅ RS ⋙ P₃)
    (hassoc : ∀ A, d₃.hom.app A ≫ P₃.map (c.hom.app A) =
      d₁.hom.app A ≫ d₂.hom.app (R.obj A))
    {A : C₁} {B : C₂} {C : C₃} (a : B ≅ R.obj A) (b : C ≅ S.obj B)
    (ab : C ≅ RS.obj A) (hab : ab = b ≪≫ S.mapIso a ≪≫ c.symm.app A) :
    (d₁.app A ≪≫ P₂.mapIso a.symm) ≪≫ (d₂.app B ≪≫ P₃.mapIso b.symm) =
      d₃.app A ≪≫ P₃.mapIso ab.symm := by
  subst ab
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom,
    Iso.symm_hom, Iso.symm_inv, Iso.app_hom, Iso.app_inv, Functor.map_comp,
    Category.assoc]
  have hn := d₂.hom.naturality a.inv
  simp only [Functor.comp_map] at hn
  rw [reassoc_of% hn, ← reassoc_of% (hassoc A)]
  rfl

namespace AlgebraicGeometry.ProEtale
universe u
open CategoryTheory

private theorem factorization_assoc (Λ : Type (u + 1)) [CommRing Λ]
    {X Y Z W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (p : X ⟶ W) (q : Y ⟶ W) (hp : f ≫ q = p) (hq : g ≫ h = q)
    (hfg : (f ≫ g) ≫ h = p)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))) :
    (factorizationIso Λ (f ≫ g) h p hfg).hom.app K ≫
        (lowerStar (ModuleCat.{u + 1} Λ) h).rightDerivedFunctor.map
          ((finiteDirectImageComposition Λ f g).hom.app K) =
      (factorizationIso Λ f q p hp).hom.app K ≫
        (factorizationIso Λ g h q hq).hom.app
          ((lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.obj K) := by
  subst p
  subst q
  have hc := congr_app (congrArg Iso.hom (finiteDirectImage_assoc Λ f g h)) K
  simpa [factorizationIso] using hc.symm

private theorem refinementProperOpen_comp
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c₁ c₂ c₃ : Compactification f}
    [IsNoetherian c₁.Z] [IsNoetherian c₂.Z] [IsNoetherian c₃.Z]
    (r : c₁ ⟶ c₂) (s : c₂ ⟶ c₃) (O : EtaleOriginDerivedCategory X Λ) :
    refinementProperOpenIso Λ (r ≫ s) O =
      refinementProperOpenIso Λ s O ≪≫
        (lowerStar (ModuleCat.{u + 1} Λ) s.hom).rightDerivedFunctor.mapIso
          (refinementProperOpenIso Λ r O) ≪≫
        (finiteDirectImageComposition Λ r.hom s.hom).symm.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) c₁.i).mapDerivedCategory.obj
            (refinementFixedObject X Λ O)) := by
  let A := ModuleCat.{u + 1} Λ
  let q := refinementFixedWitnessIso X Λ O
  have hc := properOpen_ambient_comp Λ r.hom s.hom c₁.i c₂.i c₃.i
    r.i_hom s.i_hom O.2.L
  have ht := conjugated_comp (lowerStar A r.hom).rightDerivedFunctor
    (lowerStar A s.hom).rightDerivedFunctor
    (lowerStar A (r.hom ≫ s.hom)).rightDerivedFunctor
    (finiteDirectImageComposition Λ r.hom s.hom).symm
    ((openImmersionLowerShriek A c₁.i).mapDerivedCategory.mapIso q)
    ((openImmersionLowerShriek A c₂.i).mapDerivedCategory.mapIso q)
    ((openImmersionLowerShriek A c₃.i).mapDerivedCategory.mapIso q)
    (properOpenProEtaleIso Λ r.hom c₁.i c₂.i r.i_hom O.2.L)
    (properOpenProEtaleIso Λ s.hom c₂.i c₃.i s.i_hom O.2.L)
  rw [← hc] at ht
  simpa [refinementProperOpenIso, Functor.mapIso_trans, Functor.mapIso_symm,
    Iso.trans_assoc, q, A] using ht.symm

private theorem geometric_comparison_comp (Λ : Type (u + 1)) [CommRing Λ]
    {T₁ T₂ T₃ Y : Scheme.{u}} (r : T₁ ⟶ T₂) (s : T₂ ⟶ T₃)
    (p₁ : T₁ ⟶ Y) (p₂ : T₂ ⟶ Y) (p₃ : T₃ ⟶ Y)
    (hr : r ≫ p₂ = p₁) (hs : s ≫ p₃ = p₂) (hrs : (r ≫ s) ≫ p₃ = p₁)
    (K₁ : DerivedCategory (Sheaf (Scheme.ProEt.topology T₁) (ModuleCat.{u + 1} Λ)))
    (K₂ : DerivedCategory (Sheaf (Scheme.ProEt.topology T₂) (ModuleCat.{u + 1} Λ)))
    (K₃ : DerivedCategory (Sheaf (Scheme.ProEt.topology T₃) (ModuleCat.{u + 1} Λ)))
    (a : K₂ ≅ (lowerStar (ModuleCat.{u + 1} Λ) r).rightDerivedFunctor.obj K₁)
    (b : K₃ ≅ (lowerStar (ModuleCat.{u + 1} Λ) s).rightDerivedFunctor.obj K₂) :
    ((factorizationIso Λ r p₂ p₁ hr).app K₁ ≪≫
      (lowerStar (ModuleCat.{u + 1} Λ) p₂).rightDerivedFunctor.mapIso a.symm) ≪≫
      ((factorizationIso Λ s p₃ p₂ hs).app K₂ ≪≫
        (lowerStar (ModuleCat.{u + 1} Λ) p₃).rightDerivedFunctor.mapIso b.symm) =
      (factorizationIso Λ (r ≫ s) p₃ p₁ hrs).app K₁ ≪≫
        (lowerStar (ModuleCat.{u + 1} Λ) p₃).rightDerivedFunctor.mapIso
          (b ≪≫ (lowerStar (ModuleCat.{u + 1} Λ) s).rightDerivedFunctor.mapIso a ≪≫
            (finiteDirectImageComposition Λ r s).symm.app K₁).symm := by
  exact comparison_comp
    (lowerStar (ModuleCat.{u + 1} Λ) r).rightDerivedFunctor
    (lowerStar (ModuleCat.{u + 1} Λ) s).rightDerivedFunctor
    (lowerStar (ModuleCat.{u + 1} Λ) (r ≫ s)).rightDerivedFunctor
    (lowerStar (ModuleCat.{u + 1} Λ) p₁).rightDerivedFunctor
    (lowerStar (ModuleCat.{u + 1} Λ) p₂).rightDerivedFunctor
    (lowerStar (ModuleCat.{u + 1} Λ) p₃).rightDerivedFunctor
    (finiteDirectImageComposition Λ r s)
    (factorizationIso Λ r p₂ p₁ hr) (factorizationIso Λ s p₃ p₂ hs)
    (factorizationIso Λ (r ≫ s) p₃ p₁ hrs)
    (factorization_assoc Λ r s p₃ p₁ p₂ hr hs hrs) a b _ rfl

private theorem witness_formula
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c₁ c₂ : Compactification f}
    (r : c₁ ⟶ c₂) (O : EtaleOriginDerivedCategory X Λ) :
    refinementComparisonAtWitness Λ r O =
      (factorizationIso Λ r.hom c₂.g c₁.g r.hom_g).app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) c₁.i).mapDerivedCategory.obj
            (refinementFixedObject X Λ O)) ≪≫
        (lowerStar (ModuleCat.{u + 1} Λ) c₂.g).rightDerivedFunctor.mapIso
          (refinementProperOpenIso Λ r O).symm := by
  unfold refinementComparisonAtWitness factorizationIso
  rw [NatIso.trans_app, ← Iso.trans_assoc]

/-- Composition at one retained witness, before constructing any natural transformation
or comparison through a common refinement. -/
theorem refinementComparisonAtWitness_comp
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c₁ c₂ c₃ : Compactification f}
    [IsNoetherian c₁.Z] [IsNoetherian c₂.Z] [IsNoetherian c₃.Z]
    (r : c₁ ⟶ c₂) (s : c₂ ⟶ c₃) (O : EtaleOriginDerivedCategory X Λ) :
    refinementComparisonAtWitness Λ (r ≫ s) O =
      refinementComparisonAtWitness Λ r O ≪≫ refinementComparisonAtWitness Λ s O  := by
  rw [witness_formula, witness_formula, witness_formula, refinementProperOpen_comp]
  exact (geometric_comparison_comp Λ r.hom s.hom c₁.g c₂.g c₃.g
    r.hom_g s.hom_g (r ≫ s).hom_g _ _ _
    (refinementProperOpenIso Λ r O) (refinementProperOpenIso Λ s O)).symm

end AlgebraicGeometry.ProEtale
