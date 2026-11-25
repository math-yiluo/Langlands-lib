/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfIntegralReductionTower
public import WeilConjectures.AlgebraicGeometry.Koszul.KoszulReconstructionModels
public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
import all WeilConjectures.AlgebraicGeometry.Koszul.KoszulReconstructionModels
import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulQuotientRoosAugmentation
import WeilConjectures.AlgebraicGeometry.Koszul.KoszulReconstructionLocalizationAssembly
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

/-! # Normalized Koszul reconstruction comparison

The strict completed Koszul augmentation and the exact-products Roos comparison
are assembled on K-flat complexes, then descended along localization. The unit
calculation uses the independent characterization of the quotient completion unit.

## References

* Stacks Tags 091N, 099M and 0941
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] WeilConjectures.sfAbSheafify
attribute [local instance] WeilConjectures.sfAbBijective
attribute [local instance] AlgebraicGeometry.ProEtale.VaryingRing.ringSheafify
private theorem reconstructionUnitSquare {E : Type*} [Category E]
    {X Y Z U V R : E} (k : X ⟶ Y) (f : Y ⟶ Z) (b : X ⟶ Z)
    (a : Z ⟶ U) (v : X ⟶ V) (w : V ⟶ U) (e : U ⟶ R) (δ : V ⟶ R)
    (hk : k ≫ f = b) (ha : b ≫ a = v ≫ w) (he : w ≫ e = δ) :
    k ≫ (f ≫ a ≫ e) = v ≫ δ := by
  rw [← Category.assoc, ← Category.assoc, hk, ha, Category.assoc, he]

section HomotopyComparison

variable {B C : Type*} [Category B] [Abelian B] [Category C] [Abelian C]
  [HasDerivedCategory B] [HasDerivedCategory C]
  (F : B ⥤ C) [F.Additive]
  (K : DerivedCategory B ⥤ DerivedCategory B)
  (RF : DerivedCategory C ⥤ DerivedCategory B)

private def reconstructionHomotopyMap
    (z : DerivedCategory.Q ⋙ K ⟶
      F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⋙ RF) :
    DerivedCategory.Qh ⋙ K ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⋙ RF := by
  let q := HomotopyCategory.quotient B (.up ℤ)
  let Qh := DerivedCategory.Qh (C := B)
  let FC := F.mapHomologicalComplex (.up ℤ)
  let FH := F.mapHomotopyCategory (.up ℤ)
  let H := HomotopyCategory B (.up ℤ)
  let a₀ : q ⋙ (Qh ⋙ K) ≅ DerivedCategory.Q ⋙ K :=
    (Functor.associator q Qh K).symm ≪≫
      Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso B) K
  let b₀ : q ⋙ (FH ⋙ DerivedCategory.Qh ⋙ RF) ≅ FC ⋙ DerivedCategory.Q ⋙ RF :=
    (Functor.associator q FH (DerivedCategory.Qh ⋙ RF)).symm ≪≫
      Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (.up ℤ))
        (DerivedCategory.Qh ⋙ RF) ≪≫
      Functor.associator FC (HomotopyCategory.quotient _ (.up ℤ))
        (DerivedCategory.Qh ⋙ RF) ≪≫
      Functor.isoWhiskerLeft FC
        ((Functor.associator (HomotopyCategory.quotient _ (.up ℤ))
          DerivedCategory.Qh RF).symm ≪≫
            Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso _) RF)
  let E := (Functor.whiskeringLeft _ H (DerivedCategory B)).obj q
  exact E.preimage (a₀.hom ≫ z ≫ b₀.inv)

private theorem reconstructionHomotopyMap_app
    (z : DerivedCategory.Q ⋙ K ⟶
      F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⋙ RF)
    (X : CochainComplex B ℤ) :
    (reconstructionHomotopyMap F K RF z).app
      ((HomotopyCategory.quotient B (.up ℤ)).obj X) = z.app X := by
  let q := HomotopyCategory.quotient B (.up ℤ)
  let Qh := DerivedCategory.Qh (C := B)
  let FC := F.mapHomologicalComplex (.up ℤ)
  let FH := F.mapHomotopyCategory (.up ℤ)
  let H := HomotopyCategory B (.up ℤ)
  let a₀ : q ⋙ (Qh ⋙ K) ≅ DerivedCategory.Q ⋙ K :=
    (Functor.associator q Qh K).symm ≪≫
      Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso B) K
  let b₀ : q ⋙ (FH ⋙ DerivedCategory.Qh ⋙ RF) ≅ FC ⋙ DerivedCategory.Q ⋙ RF :=
    (Functor.associator q FH (DerivedCategory.Qh ⋙ RF)).symm ≪≫
      Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (.up ℤ))
        (DerivedCategory.Qh ⋙ RF) ≪≫
      Functor.associator FC (HomotopyCategory.quotient _ (.up ℤ))
        (DerivedCategory.Qh ⋙ RF) ≪≫
      Functor.isoWhiskerLeft FC
        ((Functor.associator (HomotopyCategory.quotient _ (.up ℤ))
          DerivedCategory.Qh RF).symm ≪≫
            Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso _) RF)
  let E := (Functor.whiskeringLeft _ H (DerivedCategory B)).obj q
  change (E.map (E.preimage (a₀.hom ≫ z ≫ b₀.inv))).app X = _
  rw [E.map_preimage]
  dsimp only [a₀, b₀, NatTrans.comp_app, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
    Iso.symm_inv, Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_inv, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_map, Functor.associator_hom_app, Functor.associator_inv_app]
  have hq : (DerivedCategory.quotientCompQhIso B).hom.app X = 𝟙 _ := rfl
  have hqt : (DerivedCategory.quotientCompQhIso C).inv.app (FC.obj X) = 𝟙 _ := rfl
  have hfc : (F.mapHomotopyCategoryFactors (.up ℤ)).inv.app X = 𝟙 _ := rfl
  simp only [hq, hqt, hfc, CategoryTheory.Functor.map_id]
  simp only [Category.comp_id]
  change (𝟙 _ ≫ 𝟙 _) ≫ z.app X ≫ 𝟙 _ ≫ 𝟙 _ = z.app X
  simp only [Category.id_comp, Category.comp_id]

private theorem reconstructionModelAlpha_unitQ (L : C ⥤ B) [L.Additive]
    [Abelian.HasKInjectiveResolutions C] (u : 𝟭 B ⟶ F ⋙ L) (X : CochainComplex B ℤ) :
    (reconstructionModelAlpha F L L.rightDerivedFunctor L.rightDerivedFunctorUnit u).app
        ((HomotopyCategory.quotient B (.up ℤ)).obj X) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex u (.up ℤ)).app X) ≫
        L.rightDerivedFunctorUnitQ ((F.mapHomologicalComplex (.up ℤ)).obj X) := by
  let Y := (HomotopyCategory.quotient B (.up ℤ)).obj X
  have hid : (Functor.mapHomotopyCategoryIdIso B (.up ℤ)).inv.app Y = 𝟙 _ := by
    apply (cancel_mono ((Functor.mapHomotopyCategoryIdIso B (.up ℤ)).hom.app Y)).1
    rw [Iso.inv_hom_id_app, Functor.mapHomotopyCategoryIdIso_hom_app_eq_id,
      Category.id_comp]
    rfl
  have hcmp : (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ L)) (.up ℤ)).inv.app
      Y = 𝟙 _ := by
    apply (cancel_mono
      ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ L)) (.up ℤ)).hom.app Y)).1
    rw [Iso.inv_hom_id_app, Functor.mapHomotopyCategoryCompIso_refl_hom_app,
      Category.id_comp]
    rfl
  dsimp only [reconstructionModelAlpha, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.leftUnitor_inv_app, Functor.associator_hom_app]
  rw [hid, hcmp]
  change 𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _) ≫ _ ≫
    DerivedCategory.Qh.map (𝟙 _) ≫ 𝟙 _ ≫ _ = _
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  dsimp only [Functor.rightDerivedFunctorUnitQ]
  change _ = _ ≫ (𝟙 _ ≫ L.rightDerivedFunctorUnit.app
    ((F.mapHomotopyCategory (.up ℤ)).obj Y) ≫ L.rightDerivedFunctor.map (𝟙 _))
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  change DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex u (.up ℤ)).app X) ≫
      L.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj Y) =
    DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex u (.up ℤ)).app X) ≫
      L.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj Y) ≫ 𝟙 _
  rw [Category.comp_id]

private theorem reconstructionDerivedModelUnit_normalization
    {E : CochainComplex B ℤ → Prop} (D : DerivedReductionModelData F E)
    (L : C ⥤ B) [L.Additive]
    (δ : L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    (u : 𝟭 B ⟶ F ⋙ L) (X : CochainComplex B ℤ) (hX : E X)
    (hg : IsIso ((reconstructionModelGamma F D.reduction RF D.counit).app
      ((HomotopyCategory.quotient B (.up ℤ)).obj X))) :
    derivedCompletionModelUnit D L RF δ u X hX =
      (reconstructionModelAlpha F L RF δ u).app
          ((HomotopyCategory.quotient B (.up ℤ)).obj X) ≫
        @inv _ _ _ _ ((reconstructionModelGamma F D.reduction RF D.counit).app
          ((HomotopyCategory.quotient B (.up ℤ)).obj X)) hg := by
  have := D.isIso_counit X hX
  exact reconstructionModelUnit_normalization F L D.reduction RF D.counit δ u X
    (D.complexCounit_isIso X hX) hg

end HomotopyComparison

attribute [local irreducible] reconstructionHomotopyMap

attribute [local irreducible] completedAdicOrdinaryTower completedAdicReductionData

variable (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
/-- The strict comparison part of Koszul reconstruction: the completed Koszul derived
functor is naturally isomorphic to the derived quotient limit, with the prescribed unit
 equality. -/
theorem koszulReconstructionComparison (r : ℕ) (a : Fin r → A)
    (_ha : Ideal.span (Set.range a) = d.ideal) :
    ∃ c : reconstructionKoszulDerivedFunctor T d r a ≅
        completedAdicReduction T d ⋙ reconstructionRlim T d,
      ∀ K : DerivedCategory (CompletedAdicModules T d),
        (reconstructionKoszulDerivedUnit T d r a).app K ≫ c.hom.app K =
          (reconstructionCompletionUnit T d).app K := by
  classical
  let B := CompletedAdicModules T d
  let F := completedAdicOrdinaryTower T d
  let FC := F.mapHomologicalComplex (.up ℤ)
  let FH := F.mapHomotopyCategory (.up ℤ)
  let LF := completedAdicReduction T d
  let RF := reconstructionRlim T d
  let K := reconstructionKoszulDerivedFunctor T d r a
  let H := HomotopyCategory B (.up ℤ)
  let q := HomotopyCategory.quotient B (.up ℤ)
  let Qh := DerivedCategory.Qh (C := B)
  let P : ObjectProperty H := fun X ↦
    CochainComplex.IsAcyclicTensorKFlat (R := completedAdicCommRing T d) X.as
  let W := HomotopyCategory.quasiIso B (.up ℤ)
  let V := W.inverseImage P.ι
  let S := P.ι ⋙ Qh
  have hS : S.IsLocalization V := by
    apply reconstructionRestrictionLocalization W Qh P
    intro X
    obtain ⟨C, f, hC, _, hf, _⟩ := CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := completedAdicCommRing T d) X.as
    exact ⟨⟨q.obj C, hC⟩, q.map f,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf⟩
  have : HasExactLimitsOfShape (Discrete ℕ) B := reconstructionCountableProducts_exact T d
  let δ : ExactProductsRoos.ordinary ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF :=
    { app := (reconstructionLimit T d).rightDerivedFunctorUnitQ
      naturality := fun _ _ f ↦
        (reconstructionLimit T d).rightDerivedFunctorUnitQ_naturality f }
  obtain ⟨e, he⟩ := ExactProductsRoos.comparisonIso RF δ (by
    intro I hI
    letI := hI
    change IsIso ((reconstructionLimit T d).rightDerivedFunctorUnitQ I)
    rw [Functor.rightDerivedFunctorUnitQ_eq]
    infer_instance)
  obtain ⟨aug, haug, hu⟩ := completedKoszulQuotientRoosAugmentation T d r a _ha
  let f := Localization.fac (reconstructionKoszulFiberFunctor T d r a ⋙ DerivedCategory.Q)
    (reconstructionKoszulFiberFunctor_inverts T d r a) DerivedCategory.Q
  let z : DerivedCategory.Q ⋙ K ⟶ FC ⋙ DerivedCategory.Q ⋙ RF :=
    f.hom ≫ Functor.whiskerRight aug DerivedCategory.Q ≫
      (Functor.associator FC ExactProductsRoos.fibre DerivedCategory.Q).hom ≫
        Functor.whiskerLeft FC e.hom
  let α := reconstructionHomotopyMap F K RF z
  have hα (C : CochainComplex B ℤ) :
      α.app (q.obj C) = f.hom.app C ≫ DerivedCategory.Q.map (aug.app C) ≫
        e.hom.app (FC.obj C) := by
    rw [reconstructionHomotopyMap_app]
    change f.hom.app C ≫ DerivedCategory.Q.map (aug.app C) ≫
      𝟙 _ ≫ e.hom.app (FC.obj C) = _
    rw [Category.id_comp]
  let γ := reconstructionModelGamma F LF RF (completedAdicReductionData T d).counit
  have hγ (X : P.FullSubcategory) : IsIso (γ.app X.obj) := by
    letI : IsIso ((completedAdicReductionData T d).counit.app X.obj) :=
      (completedAdicReductionData T d).isIso_counit X.obj.as X.property
    change IsIso ((reconstructionModelGamma F LF RF
      (completedAdicReductionData T d).counit).app X.obj)
    dsimp only [reconstructionModelGamma, NatTrans.comp_app,
      Functor.associator_inv_app, Functor.associator_hom_app, Functor.whiskerRight_app]
    infer_instance
  have hαiso (X : P.FullSubcategory) : IsIso (α.app X.obj) := by
    have hx := haug X.obj.as X.property
    letI : IsIso (e.hom.app (FC.obj X.obj.as)) := inferInstance
    letI : IsIso (f.hom.app X.obj.as) := inferInstance
    letI : QuasiIso (aug.app X.obj.as) := hx
    letI : IsIso (DerivedCategory.Q.map (aug.app X.obj.as)) := inferInstance
    rw [show α.app X.obj = f.hom.app X.obj.as ≫ DerivedCategory.Q.map (aug.app X.obj.as) ≫
      e.hom.app (FC.obj X.obj.as) from hα X.obj.as]
    infer_instance
  obtain ⟨c, hc, _⟩ := reconstructionDescendUnit P Qh W K (LF ⋙ RF)
    (FH ⋙ DerivedCategory.Qh ⋙ RF) α γ hγ
  have hcrest (X : P.FullSubcategory) : IsIso (c.app (Qh.obj X.obj)) := by
    rw [hc X]
    infer_instance
  obtain ⟨eiso, heiso⟩ := localizationNatTransIso P Qh W K (LF ⋙ RF) c hcrest
  have hunit : ∀ X : P.FullSubcategory,
      (reconstructionKoszulDerivedUnit T d r a).app (Qh.obj X.obj) ≫
          eiso.hom.app (Qh.obj X.obj) =
        (reconstructionCompletionUnit T d).app (Qh.obj X.obj) := by
    intro X
    let L := reconstructionLimit T d
    let u := reconstructionOrdinaryUnit T d
    let δh := L.rightDerivedFunctorUnit
    have hk : (reconstructionKoszulDerivedUnit T d r a).app
        (DerivedCategory.Q.obj X.obj.as) ≫ f.hom.app X.obj.as =
          DerivedCategory.Q.map (completedAdicKoszulUnitComplex T d r a X.obj.as) := by
      dsimp [reconstructionKoszulDerivedUnit]
      rw [Localization.liftNatTrans_app]
      change (𝟙 _ ≫ DerivedCategory.Q.map
        (completedAdicKoszulUnitComplex T d r a X.obj.as) ≫ f.inv.app X.obj.as) ≫
          f.hom.app X.obj.as = _
      simp only [Category.id_comp, Category.assoc, Iso.inv_hom_id_app]
      exact Category.comp_id _
    have hr := congrArg (fun η ↦ η.app (FC.obj X.obj.as)) he
    change DerivedCategory.Q.map (ExactProductsRoos.comparison.app (FC.obj X.obj.as)) ≫
      e.hom.app (FC.obj X.obj.as) = δ.app (FC.obj X.obj.as) at hr
    have hm : (reconstructionKoszulDerivedUnit T d r a).app (Qh.obj X.obj) ≫
        α.app X.obj = (reconstructionModelAlpha F L RF δh u).app X.obj := by
      have hαX : α.app X.obj = f.hom.app X.obj.as ≫
          DerivedCategory.Q.map (aug.app X.obj.as) ≫ e.hom.app (FC.obj X.obj.as) :=
        hα X.obj.as
      have hs := congrArg DerivedCategory.Q.map (hu X.obj.as)
      have hs' : DerivedCategory.Q.map
          (completedAdicKoszulUnitComplex T d r a X.obj.as) ≫
            DerivedCategory.Q.map (aug.app X.obj.as) =
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex u (.up ℤ)).app X.obj.as) ≫
            DerivedCategory.Q.map (ExactProductsRoos.comparison.app (FC.obj X.obj.as)) :=
        (DerivedCategory.Q.map_comp _ _).symm.trans
          (hs.trans (DerivedCategory.Q.map_comp _ _))
      have hx := reconstructionUnitSquare _ _ _ _ _ _ _ _ hk hs' hr
      exact (congrArg ((reconstructionKoszulDerivedUnit T d r a).app (Qh.obj X.obj) ≫ ·)
        hαX).trans (hx.trans (reconstructionModelAlpha_unitQ F L u X.obj.as).symm)
    have hn := reconstructionDerivedModelUnit_normalization F RF
      (completedAdicReductionData T d) L δh u X.obj.as X.property (hγ X)
    have hcomp := (reconstructionCompletionUnit_exists T d).exists.choose_spec
      X.obj.as X.property
    change reconstructionUnitOnKFlat T d X.obj.as X.property =
      (reconstructionModelAlpha F L RF δh u).app X.obj ≫ inv (γ.app X.obj) at hn
    rw [heiso, hc X, ← Category.assoc, hm]
    exact hn.symm.trans hcomp.symm
  have hunit_all := localizationUnitEq P Qh W K (LF ⋙ RF) (𝟭 _) eiso
    (reconstructionKoszulDerivedUnit T d r a)
      (reconstructionCompletionUnit T d) hunit
  refine ⟨eiso, ?_⟩
  intro Kobj
  exact hunit_all Kobj

end AlgebraicGeometry.Scheme
