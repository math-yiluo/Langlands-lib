/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.CyclicDerivedHomData
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.AdjunctionShift

/-! # Right-derived transport of cyclic presentations

Source: Stacks Project, Derived Categories, Tags 070I, 070K, 070Y and 0152;
the right-derived companion proof plan in CyclicDerivedHomExactSequence.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u v w wF uD vD wD wG

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u} [Category.{v} C] [Abelian C]
  (F : C ⥤ C) [F.Additive] [F.IsEquivalence]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{wF} (IsoAlgebra F)]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  (G : D ⥤ D) [G.Additive] [G.IsEquivalence]
  [HasDerivedCategory.{wD} D] [HasDerivedCategory.{wG} (IsoAlgebra G)]
  (L : C ⥤ D) [L.Additive] (e : L ⋙ G ≅ F ⋙ L)
  [IsGrothendieckAbelian.{v} C] [IsGrothendieckAbelian.{vD} D]
  [PreservesFiniteLimits L]
  (hF : ∀ K : CochainComplex (IsoAlgebra F) ℤ,
    ∃ (I : CochainComplex (IsoAlgebra F) ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)
  (hC : ∀ K : CochainComplex C ℤ,
    ∃ (I : CochainComplex C ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)
  [(L.rightDerivedFunctorOfQuasiIsoResolutions hC).CommShift ℤ]
  (hσ : NatTrans.CommShift (L.rightDerivedFunctorOfQuasiIsoResolutionsUnit hC) ℤ)

private theorem conjugation_transport
    {A B : Type*} [Category A] [Category B] [HasShift A ℤ] [HasShift B ℤ]
    (P : A ⥤ A) (R : B ⥤ B) (H : A ⥤ B)
    [P.CommShift ℤ] [R.CommShift ℤ] [H.CommShift ℤ]
    (β : H ⋙ R ≅ P ⋙ H) [NatTrans.CommShift β.hom ℤ]
    {XM XN : A} {YM YN : B}
    (θM : P.obj XM ≅ XM) (θN : P.obj XN ≅ XN)
    (ψM : R.obj YM ≅ YM) (ψN : R.obj YN ≅ YN)
    (αM : YM ≅ H.obj XM) (αN : YN ≅ H.obj XN)
    (hM : R.map αM.hom ≫ β.hom.app XM ≫ H.map θM.hom = ψM.hom ≫ αM.hom)
    (hN : R.map αN.hom ≫ β.hom.app XN ≫ H.map θN.hom = ψN.hom ≫ αN.hom)
    (r : ℤ) (u : XM ⟶ XN⟦r⟧) :
    αM.hom ≫ H.map (θM.inv ≫ P.map u ≫ (P.commShiftIso r).hom.app XN ≫
        θN.hom⟦r⟧') ≫ (H.commShiftIso r).hom.app XN ≫ αN.inv⟦r⟧' =
      ψM.inv ≫ R.map (αM.hom ≫ H.map u ≫ (H.commShiftIso r).hom.app XN ≫
        αN.inv⟦r⟧') ≫ (R.commShiftIso r).hom.app YN ≫ ψN.hom⟦r⟧' := by
  have hMi : αM.hom ≫ H.map θM.inv =
      ψM.inv ≫ R.map αM.hom ≫ β.hom.app XM := by
    have h := congrArg (fun f ↦ ψM.inv ≫ f ≫ H.map θM.inv) hM
    simp only [Category.assoc, ← H.map_comp, Iso.hom_inv_id, H.map_id,
      Iso.inv_hom_id_assoc] at h
    erw [Category.comp_id] at h
    exact h.symm
  have hNi : β.hom.app XN ≫ H.map θN.hom ≫ αN.inv =
      R.map αN.inv ≫ ψN.hom := by
    have h := congrArg (fun f ↦ R.map αN.inv ≫ f ≫ αN.inv) hN
    simpa only [Category.assoc, ← R.map_comp_assoc, Iso.inv_hom_id, R.map_id,
      Category.id_comp, Iso.hom_inv_id, Category.comp_id] using h
  have hb := NatTrans.shift_app_comm β.hom r XN
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc] at hb
  dsimp only [Functor.comp_map, Functor.comp_obj] at hb
  have ht := congrArg (fun f ↦ f⟦r⟧') hNi
  simp only [Functor.map_comp] at ht
  simp only [H.map_comp, R.map_comp, Category.assoc]
  rw [reassoc_of% hMi, ← reassoc_of% (β.hom.naturality u)]
  rw [H.commShiftIso_hom_naturality_assoc, ← reassoc_of% hb, ht]
  rw [← R.commShiftIso_hom_naturality_assoc]

private def homotopyComparison :
    L.mapHomotopyCategory (.up ℤ) ⋙ G.mapHomotopyCategory (.up ℤ) ≅
      F.mapHomotopyCategory (.up ℤ) ⋙ L.mapHomotopyCategory (.up ℤ) :=
  Functor.mapHomotopyCategoryCompIso e (.up ℤ) ≪≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ L)) (.up ℤ)).symm

omit [HasDerivedCategory (IsoAlgebra F)] [HasDerivedCategory (IsoAlgebra G)]
  [IsGrothendieckAbelian.{vD} D] [PreservesFiniteLimits L] in
include e hσ in
private theorem right_action_comparison :
    ∃ β : L.rightDerivedFunctorOfQuasiIsoResolutions hC ⋙ G.mapDerivedCategory ≅
      F.mapDerivedCategory ⋙ L.rightDerivedFunctorOfQuasiIsoResolutions hC,
      NatTrans.CommShift β.hom ℤ ∧
      ∀ K : HomotopyCategory C (.up ℤ),
        G.mapDerivedCategory.map
            ((L.rightDerivedFunctorOfQuasiIsoResolutionsUnit hC).app K) ≫
          β.hom.app (DerivedCategory.Qh.obj K) ≫
          (L.rightDerivedFunctorOfQuasiIsoResolutions hC).map
            (F.mapDerivedCategoryFactorsh.hom.app K) =
        G.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj K) ≫
          DerivedCategory.Qh.map ((homotopyComparison F G L e).hom.app K) ≫
          (L.rightDerivedFunctorOfQuasiIsoResolutionsUnit hC).app
            ((F.mapHomotopyCategory (.up ℤ)).obj K) := by
  let H := L.rightDerivedFunctorOfQuasiIsoResolutions hC
  let η := L.rightDerivedFunctorOfQuasiIsoResolutionsUnit hC
  let Lh := L.mapHomotopyCategory (.up ℤ)
  let Fh := F.mapHomotopyCategory (.up ℤ)
  let Gh := G.mapHomotopyCategory (.up ℤ)
  let eh : Lh ⋙ Gh ≅ Fh ⋙ Lh := homotopyComparison F G L e
  let a : Lh ⋙ DerivedCategory.Qh ⋙ G.mapDerivedCategory ⟶
      DerivedCategory.Qh ⋙ H ⋙ G.mapDerivedCategory :=
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight η G.mapDerivedCategory ≫
      (Functor.associator _ _ _).hom
  let b : Lh ⋙ DerivedCategory.Qh ⋙ G.mapDerivedCategory ⟶
      DerivedCategory.Qh ⋙ F.mapDerivedCategory ⋙ H :=
    Functor.whiskerLeft Lh G.mapDerivedCategoryFactorsh.hom ≫
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight eh.hom DerivedCategory.Qh ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft Fh η ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight F.mapDerivedCategoryFactorsh.inv H ≫
      (Functor.associator _ _ _).hom
  have ha : (H ⋙ G.mapDerivedCategory).IsRightDerivedFunctor a
      (HomotopyCategory.quasiIso C (.up ℤ)) := by
    refine (HomotopyCategory.KInjectives.localizerMorphism_derives
      (Lh ⋙ DerivedCategory.Qh ⋙ G.mapDerivedCategory)).isRightDerivedFunctor_of_isIso _
      (fun X ↦ ?_)
    obtain ⟨K, hK, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective X
    have hη := L.rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso hC K
    have : IsIso (η.app ((HomotopyCategory.quotient C (.up ℤ)).obj K)) := hη
    dsimp only [a, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp]
    change IsIso (𝟙 _ ≫ G.mapDerivedCategory.map
      (η.app ((HomotopyCategory.quotient C (.up ℤ)).obj K)) ≫ 𝟙 _)
    infer_instance
  have hb : (F.mapDerivedCategory ⋙ H).IsRightDerivedFunctor b
      (HomotopyCategory.quasiIso C (.up ℤ)) := by
    refine (HomotopyCategory.KInjectives.localizerMorphism_derives
      (Lh ⋙ DerivedCategory.Qh ⋙ G.mapDerivedCategory)).isRightDerivedFunctor_of_isIso _
      (fun X ↦ ?_)
    obtain ⟨K, hK, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective X
    have hη := L.rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso hC
      ((F.mapHomologicalComplex (.up ℤ)).obj K)
    have : IsIso (η.app (Fh.obj ((HomotopyCategory.quotient C (.up ℤ)).obj K))) :=
      (NatTrans.isIso_app_iff_of_iso η ((F.mapHomotopyCategoryFactors (.up ℤ)).app K)).mpr hη
    dsimp only [b, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app]
    change IsIso (b.app ((HomotopyCategory.quotient C (.up ℤ)).obj K))
    dsimp only [b, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app]
    infer_instance
  let β := Functor.rightDerivedUnique (H ⋙ G.mapDerivedCategory)
    (F.mapDerivedCategory ⋙ H) a b (HomotopyCategory.quasiIso C (.up ℤ))
  have hβ : a ≫ Functor.whiskerLeft DerivedCategory.Qh β.hom = b := by
    simp only [β, Functor.rightDerivedUnique, Functor.rightDerivedNatIso_hom,
      Functor.rightDerivedNatTrans_fac, Iso.refl_hom, Category.id_comp]
  have : NatTrans.CommShift η ℤ := hσ
  have : NatTrans.CommShift a ℤ := by dsimp only [a]; infer_instance
  have : NatTrans.CommShift b ℤ := by
    dsimp only [b, eh, homotopyComparison, Iso.trans_hom]
    infer_instance
  have : IsIso (Functor.whiskerLeft
      (ObjectProperty.ι (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal) a) := by
    exact @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (fun X ↦ by
    obtain ⟨K, hK, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective X
    have hη := L.rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso hC K
    have : IsIso (η.app ((HomotopyCategory.quotient C (.up ℤ)).obj K)) := hη
    dsimp only [Functor.whiskerLeft_app, a, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp]
    change IsIso (𝟙 _ ≫ G.mapDerivedCategory.map
      (η.app ((HomotopyCategory.quotient C (.up ℤ)).obj K)) ≫ 𝟙 _)
    infer_instance)
  have : NatTrans.CommShift (a ≫ Functor.whiskerLeft DerivedCategory.Qh β.hom) ℤ := by
    rw [hβ]
    infer_instance
  refine ⟨β, NatTrans.CommShift.of_comp_whiskerLeft_Qh a β.hom, ?_⟩
  intro K
  have ht := congrArg (fun f ↦ f ≫
    H.map (F.mapDerivedCategoryFactorsh.hom.app K)) (congr_app hβ K)
  simp only [a, b, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc,
    ← H.map_comp, Iso.inv_hom_id_app, H.map_id] at ht
  erw [Category.comp_id] at ht
  exact ht

omit [IsGrothendieckAbelian.{v} C] in
private theorem structure_fach (K : HomotopyCategory (IsoAlgebra F) (.up ℤ)) :
    (cyclicDerivedStructure F).hom.app (DerivedCategory.Qh.obj K) ≫
        (forget F).mapDerivedCategoryFactorsh.hom.app K =
      F.mapDerivedCategory.map ((forget F).mapDerivedCategoryFactorsh.hom.app K) ≫
        F.mapDerivedCategoryFactorsh.hom.app
          (((forget F).mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory (strNatIso F).hom (.up ℤ)).app K) := by
  change ((Functor.mapDerivedCategoryCompIso (forget F) F).hom.app _ ≫
      (Functor.mapDerivedCategoryNatIso (strNatIso F)).hom.app _) ≫ _ = _
  rw [Category.assoc, Functor.mapDerivedCategoryNatIso_fach]
  rw [← Functor.mapDerivedCategoryCompIso_hom_app_factorsh (forget F) F K]
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

omit [F.IsEquivalence] [HasDerivedCategory C] [HasDerivedCategory (IsoAlgebra F)]
  [G.IsEquivalence] [HasDerivedCategory (IsoAlgebra G)]
  [IsGrothendieckAbelian.{v} C] [IsGrothendieckAbelian.{vD} D]
  [PreservesFiniteLimits L] in
private theorem forget_comparison_identity
    (K : HomotopyCategory (IsoAlgebra F) (.up ℤ)) :
    DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso (mapOfNatIsoCompForgetIso e)
          (.up ℤ)).hom.app K) ≫
      DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso (Iso.refl (forget F ⋙ L))
          (.up ℤ)).inv.app K) = 𝟙 _ := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  change DerivedCategory.Qh.map
      ((HomotopyCategory.quotient D (.up ℤ)).map (𝟙 _)) ≫
    DerivedCategory.Qh.map
      ((HomotopyCategory.quotient D (.up ℤ)).map (𝟙 _)) = 𝟙 _
  simp only [Functor.map_id, Category.comp_id]

omit [F.IsEquivalence] [HasDerivedCategory C] [HasDerivedCategory (IsoAlgebra F)]
  [G.IsEquivalence] [HasDerivedCategory D] [HasDerivedCategory (IsoAlgebra G)]
  [IsGrothendieckAbelian.{v} C] [IsGrothendieckAbelian.{vD} D]
  [PreservesFiniteLimits L] in
private theorem homotopy_structure
    (K : HomotopyCategory (IsoAlgebra F) (.up ℤ)) :
    (homotopyComparison F G L e).hom.app
        (((forget F).mapHomotopyCategory (.up ℤ)).obj K) ≫
      (L.mapHomotopyCategory (.up ℤ)).map
        ((NatTrans.mapHomotopyCategory (strNatIso F).hom (.up ℤ)).app K) =
      (NatTrans.mapHomotopyCategory (strNatIso G).hom (.up ℤ)).app
        (((mapOfNatIso e).mapHomotopyCategory (.up ℤ)).obj K) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  change ((HomotopyCategory.quotient D (.up ℤ)).map
      ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app
        (((forget F).mapHomologicalComplex (.up ℤ)).obj K)) ≫
      (HomotopyCategory.quotient D (.up ℤ)).map (𝟙 _)) ≫
    (HomotopyCategory.quotient D (.up ℤ)).map
      ((L.mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (strNatIso F).hom (.up ℤ)).app K)) =
    (HomotopyCategory.quotient D (.up ℤ)).map
      ((NatTrans.mapHomologicalComplex (strNatIso G).hom (.up ℤ)).app
        (((mapOfNatIso e).mapHomologicalComplex (.up ℤ)).obj K))
  simp only [Functor.map_id, Category.comp_id, ← Functor.map_comp]
  congr 1

private theorem derived_ext_on_injectives
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    {B : Type*} [Category B]
    (h : ∀ K : CochainComplex A ℤ,
      ∃ (I : CochainComplex A ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)
    {S T : DerivedCategory A ⥤ B} (a b : S ⟶ T)
    (he : ∀ (I : CochainComplex A ℤ), I.IsKInjective →
      a.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (.up ℤ)).obj I)) =
        b.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (.up ℤ)).obj I))) :
    a = b := by
  apply Localization.natTrans_ext DerivedCategory.Qh (HomotopyCategory.quasiIso A (.up ℤ))
  intro K
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  obtain ⟨I, s, hI, hs⟩ := h K
  have : IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient A (.up ℤ)).map s)) :=
    (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso A) s).2 inferInstance
  apply (cancel_mono (T.map (DerivedCategory.Qh.map
    ((HomotopyCategory.quotient A (.up ℤ)).map s)))).1
  have ha := a.naturality (DerivedCategory.Qh.map
    ((HomotopyCategory.quotient A (.up ℤ)).map s))
  have hb := b.naturality (DerivedCategory.Qh.map
    ((HomotopyCategory.quotient A (.up ℤ)).map s))
  rw [← ha, ← hb, he I hI]

omit [(L.rightDerivedFunctorOfQuasiIsoResolutions hC).CommShift ℤ] in
private theorem right_action_structure
    (β : L.rightDerivedFunctorOfQuasiIsoResolutions hC ⋙ G.mapDerivedCategory ≅
      F.mapDerivedCategory ⋙ L.rightDerivedFunctorOfQuasiIsoResolutions hC)
    (hβ : ∀ K : HomotopyCategory C (.up ℤ),
      G.mapDerivedCategory.map
          ((L.rightDerivedFunctorOfQuasiIsoResolutionsUnit hC).app K) ≫
        β.hom.app (DerivedCategory.Qh.obj K) ≫
        (L.rightDerivedFunctorOfQuasiIsoResolutions hC).map
          (F.mapDerivedCategoryFactorsh.hom.app K) =
      G.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((homotopyComparison F G L e).hom.app K) ≫
        (L.rightDerivedFunctorOfQuasiIsoResolutionsUnit hC).app
          ((F.mapHomotopyCategory (.up ℤ)).obj K))
    (M : DerivedCategory (IsoAlgebra F)) :
    G.mapDerivedCategory.map
        ((cyclicDerivedRightForgetComparison F G L e hF hC).hom.app M) ≫
      β.hom.app ((forget F).mapDerivedCategory.obj M) ≫
      (L.rightDerivedFunctorOfQuasiIsoResolutions hC).map
        ((cyclicDerivedStructure F).hom.app M) =
    (cyclicDerivedStructure G).hom.app
        (((mapOfNatIso e).rightDerivedFunctorOfQuasiIsoResolutions hF).obj M) ≫
      (cyclicDerivedRightForgetComparison F G L e hF hC).hom.app M := by
  let H := L.rightDerivedFunctorOfQuasiIsoResolutions hC
  let J := (mapOfNatIso e).rightDerivedFunctorOfQuasiIsoResolutions hF
  let η := L.rightDerivedFunctorOfQuasiIsoResolutionsUnit hC
  let ζ := (mapOfNatIso e).rightDerivedFunctorOfQuasiIsoResolutionsUnit hF
  let U := forget F
  let V := forget G
  let R := G.mapDerivedCategory
  let α := cyclicDerivedRightForgetComparison F G L e hF hC
  let θ := cyclicDerivedStructure F
  let ψ := cyclicDerivedStructure G
  have hα (K : HomotopyCategory (IsoAlgebra F) (.up ℤ)) :
      V.mapDerivedCategory.map (ζ.app K) ≫ α.hom.app (DerivedCategory.Qh.obj K) ≫
        H.map (U.mapDerivedCategoryFactorsh.hom.app K) =
      V.mapDerivedCategoryFactorsh.hom.app
          (((mapOfNatIso e).mapHomotopyCategory (.up ℤ)).obj K) ≫
        η.app ((U.mapHomotopyCategory (.up ℤ)).obj K) := by
    have ht := (Classical.choose_spec
      (exists_fixedPairDerivedForgetComparison F G L e hF hC)).1 K
    rw [← Category.assoc _ _ (η.app ((U.mapHomotopyCategory (.up ℤ)).obj K)),
      forget_comparison_identity F G L e K] at ht
    erw [Category.id_comp] at ht
    exact ht
  suffices he :
      Functor.whiskerRight α.hom R ≫
          Functor.whiskerLeft U.mapDerivedCategory β.hom ≫
          Functor.whiskerRight θ.hom H =
        Functor.whiskerLeft J ψ.hom ≫ α.hom by
    exact congr_app he M
  apply derived_ext_on_injectives hF
  intro I hI
  let K := (HomotopyCategory.quotient (IsoAlgebra F) (.up ℤ)).obj I
  let UK := (U.mapHomotopyCategory (.up ℤ)).obj K
  let AK := ((mapOfNatIso e).mapHomotopyCategory (.up ℤ)).obj K
  have : IsIso (ζ.app K) :=
    (mapOfNatIso e).rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso hF I
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  apply (cancel_mono (H.map (U.mapDerivedCategoryFactorsh.hom.app K))).1
  apply (cancel_epi (R.map (V.mapDerivedCategory.map (ζ.app K)))).1
  have hnβ := β.hom.naturality (U.mapDerivedCategoryFactorsh.hom.app K)
  have hnψ := ψ.hom.naturality (ζ.app K)
  have hnη := η.naturality
    ((NatTrans.mapHomotopyCategory (strNatIso F).hom (.up ℤ)).app K)
  dsimp only [Functor.comp_map] at hnβ hnψ hnη
  simp only [Category.assoc]
  rw [← H.map_comp, structure_fach F K]
  simp only [H.map_comp]
  rw [← reassoc_of% hnβ, ← R.map_comp_assoc, ← R.map_comp_assoc]
  simp only [Category.assoc]
  rw [hα]
  simp only [R.map_comp, Category.assoc]
  rw [reassoc_of% (hβ UK)]
  erw [← hnη]
  rw [← DerivedCategory.Qh.map_comp_assoc, homotopy_structure F G L e K]
  rw [reassoc_of% hnψ, hα, reassoc_of% (structure_fach G AK)]
  rfl

include hσ in
/-- Right-derived transport with a unit-compatible shift commutes with cyclic conjugation.

Proof: construct beta : RL ⋙ D(G) ≅ D(F) ⋙ RL by uniqueness of right derivation.
The two comparison units are invertible on K-injectives, since the exact
source autoequivalence preserves K-injectives. Their shift equations imply that
beta commutes with shifts. Next compare the two composites from D(G)D(U')R(L~)
to RL D(U). It suffices to test on K-injective fixed-pair complexes. Precompose
with D(G)D(U') of the computation unit and postcompose with RL of the forgetting
factorization. The normalized equations for alpha and beta reduce the assertion
to naturality of the RL unit and the termwise structure equation defining L~.
Cancel these invertible factors and extend along K-injective resolutions. Finally
expand the two conjugations: the structure equation at M moves the inverse
structure past alpha; naturality of beta moves the arbitrary derived morphism;
its shift equation and the structure equation at N identify the remaining factors.
Thus no representation of the arbitrary degree-r morphism is required.
Source: the action calculation in the parent right-derived companion, and the comparison of
lem-sf-fixed-pair-derived-forget-comparison; Stacks Tags 070I, 070K and 070Y.
(blueprint: lem-sf-cyclic-derived-right-action). -/
theorem cyclicDerivedHomTransport_rightDerived_action
    (M N : DerivedCategory (IsoAlgebra F)) (r : ℤ)
    (u : CyclicDerivedHom F M N r) :
    cyclicDerivedHomTransport F G
      ((mapOfNatIso e).rightDerivedFunctorOfQuasiIsoResolutions hF)
      (L.rightDerivedFunctorOfQuasiIsoResolutions hC)
      (fun r ↦ (L.rightDerivedFunctorOfQuasiIsoResolutions hC).commShiftIso r)
      (cyclicDerivedRightForgetComparison F G L e hF hC) M N r
      (cyclicDerivedHomAction F M N r u) =
      cyclicDerivedHomAction G
        (((mapOfNatIso e).rightDerivedFunctorOfQuasiIsoResolutions hF).obj M)
        (((mapOfNatIso e).rightDerivedFunctorOfQuasiIsoResolutions hF).obj N) r
        (cyclicDerivedHomTransport F G
          ((mapOfNatIso e).rightDerivedFunctorOfQuasiIsoResolutions hF)
          (L.rightDerivedFunctorOfQuasiIsoResolutions hC)
          (fun r ↦ (L.rightDerivedFunctorOfQuasiIsoResolutions hC).commShiftIso r)
          (cyclicDerivedRightForgetComparison F G L e hF hC) M N r u) := by
  obtain ⟨β, hβs, hβ⟩ := right_action_comparison F G L e hC hσ
  have : NatTrans.CommShift β.hom ℤ := hβs
  have action_apply (M N : DerivedCategory (IsoAlgebra F)) (r : ℤ)
      (u : CyclicDerivedHom F M N r) :
      cyclicDerivedHomAction F M N r u =
        ((cyclicDerivedStructure F).inv.app M ≫ F.mapDerivedCategory.map u) ≫
          ((F.mapDerivedCategory.commShiftIso r).hom.app
              ((forget F).mapDerivedCategory.obj N) ≫
            ((cyclicDerivedStructure F).hom.app N)⟦r⟧') := rfl
  simp only [cyclicDerivedHomTransport, action_apply]
  change _ = (((cyclicDerivedStructure G).inv.app _ ≫ G.mapDerivedCategory.map _) ≫ _)
  simpa only [Category.assoc, Iso.app_hom, Iso.app_inv] using
    conjugation_transport F.mapDerivedCategory G.mapDerivedCategory
      (L.rightDerivedFunctorOfQuasiIsoResolutions hC) β
      ((cyclicDerivedStructure F).app M) ((cyclicDerivedStructure F).app N)
      ((cyclicDerivedStructure G).app
        (((mapOfNatIso e).rightDerivedFunctorOfQuasiIsoResolutions hF).obj M))
      ((cyclicDerivedStructure G).app
        (((mapOfNatIso e).rightDerivedFunctorOfQuasiIsoResolutions hF).obj N))
      ((cyclicDerivedRightForgetComparison F G L e hF hC).app M)
      ((cyclicDerivedRightForgetComparison F G L e hF hC).app N)
      (right_action_structure F G L e hF hC β hβ M)
      (right_action_structure F G L e hF hC β hβ N) r u

end CategoryTheory.Endofunctor.IsoAlgebra
