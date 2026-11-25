/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedLocalIsomorphismSheaf
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedMorphismSheafComparison
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
public import WeilConjectures.ConstructibleSheaf.EtaleMorphismDescent
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale

import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Source-site evaluation of local derived isomorphisms

The local Isom presheaf formed using the small sites of source schemes is naturally
isomorphic to the presheaf formed using slice sites. This supplies canonical evaluation
on affine weakly contractible pro-etale objects, with no local-existence hypothesis.

Source: Stacks Project, Tags 09BV and 0F63; localization of the etale and pro-etale sites.
(blueprint: def-weil-pbc-source-derived-isomorphism-evaluation).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
universe u₀ u₁ u₂ u₃ u₄ v₀ v₁ v₂ v₃ v₄
namespace CategoryTheory.Functor
variable {C₀ : Type u₀} {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄}
  [Category.{v₀} C₀] [Category.{v₁} C₁] [Category.{v₂} C₂]
  [Category.{v₃} C₃] [Category.{v₄} C₄]
  [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄]
  [HasDerivedCategory C₀] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
  [HasDerivedCategory C₃] [HasDerivedCategory C₄]
  (Rv : C₀ ⥤ C₁) (Sv : C₁ ⥤ C₂) (Lv : C₀ ⥤ C₂)
  (Rw : C₀ ⥤ C₃) (Sw : C₃ ⥤ C₄) (Lw : C₀ ⥤ C₄)
  (M : C₃ ⥤ C₁) (L : C₄ ⥤ C₂)
  [Rv.Additive] [Sv.Additive] [Lv.Additive] [Rw.Additive]
  [Sw.Additive] [Lw.Additive] [M.Additive] [L.Additive]
  [PreservesFiniteLimits Rv] [PreservesFiniteColimits Rv]
  [PreservesFiniteLimits Sv] [PreservesFiniteColimits Sv]
  [PreservesFiniteLimits Lv] [PreservesFiniteColimits Lv]
  [PreservesFiniteLimits Rw] [PreservesFiniteColimits Rw]
  [PreservesFiniteLimits Sw] [PreservesFiniteColimits Sw]
  [PreservesFiniteLimits Lw] [PreservesFiniteColimits Lw]
  [PreservesFiniteLimits M] [PreservesFiniteColimits M]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  (ev : Rv ⋙ Sv ≅ Lv) (ew : Rw ⋙ Sw ≅ Lw)
  (β : Rv ≅ Rw ⋙ M) (α : M ⋙ Sv ≅ Sw ⋙ L) (δ : Lv ≅ Lw ⋙ L)
  (h : ∀ K, ev.hom.app K ≫ δ.hom.app K =
    Sv.map (β.hom.app K) ≫ α.hom.app (Rw.obj K) ≫ L.map (ew.hom.app K))

include h in
set_option backward.isDefEq.respectTransparency false in
private theorem derived_path_coherence (K : DerivedCategory C₀) :
    ((mapDerivedCategoryCompIso Rv Sv).hom.app K ≫
      (mapDerivedCategoryNatIso ev).hom.app K) ≫
        (mapDerivedCategoryTriangleIso δ).hom.app K =
    Sv.mapDerivedCategory.map ((mapDerivedCategoryTriangleIso β).hom.app K) ≫
      (mapDerivedCategorySquareIso α).hom.app (Rw.mapDerivedCategory.obj K) ≫
      L.mapDerivedCategory.map ((mapDerivedCategoryCompIso Rw Sw).hom.app K ≫
        (mapDerivedCategoryNatIso ew).hom.app K) := by
  have hh : ev ≪≫ δ = isoWhiskerRight β Sv ≪≫
      isoWhiskerLeft Rw α ≪≫ isoWhiskerRight ew L := by
    apply Iso.ext
    apply NatTrans.ext
    funext K
    exact h K
  have hd := congrArg (fun e ↦ (mapDerivedCategoryNatIso e).hom.app K) hh
  simp only [mapDerivedCategoryNatIso_trans, NatTrans.comp_app] at hd
  have hβ := congr_app (mapDerivedCategoryNatIso_isoWhiskerRight β Sv) K
  have hα := congr_app (mapDerivedCategoryNatIso_isoWhiskerLeft Rw α) K
  have hew := congr_app (mapDerivedCategoryNatIso_isoWhiskerRight ew L) K
  have ha₁ := congr_app (mapDerivedCategoryCompIso_assoc Rw M Sv) K
  have ha₂ := congr_app (mapDerivedCategoryCompIso_assoc Rw Sw L) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    at hβ hα hew ha₁ ha₂
  have ha₁' :
      Sv.mapDerivedCategory.map ((mapDerivedCategoryCompIso Rw M).inv.app K) ≫
        (mapDerivedCategoryCompIso M Sv).hom.app (Rw.mapDerivedCategory.obj K) =
      (mapDerivedCategoryCompIso (Rw ⋙ M) Sv).hom.app K ≫
        (mapDerivedCategoryCompIso Rw (M ⋙ Sv)).inv.app K := by
    apply (cancel_epi ((mapDerivedCategoryCompIso (Rw ⋙ M) Sv).inv.app K)).mp
    simp only [Iso.inv_hom_id_app_assoc]
    rw [← reassoc_of% ha₁]
    simp
  have hβ' :
      Sv.mapDerivedCategory.map ((mapDerivedCategoryNatIso β).hom.app K) ≫
        (mapDerivedCategoryCompIso (Rw ⋙ M) Sv).hom.app K =
      (mapDerivedCategoryCompIso Rv Sv).hom.app K ≫
        (mapDerivedCategoryNatIso (isoWhiskerRight β Sv)).hom.app K := by
    apply (cancel_epi ((mapDerivedCategoryCompIso Rv Sv).inv.app K)).mp
    simp only [Iso.inv_hom_id_app_assoc]
    rw [← reassoc_of% hβ]
    simp
  have ha₂' :
      (mapDerivedCategoryCompIso Rw (Sw ⋙ L)).inv.app K ≫
        (mapDerivedCategoryCompIso Sw L).inv.app (Rw.mapDerivedCategory.obj K) ≫
        L.mapDerivedCategory.map ((mapDerivedCategoryCompIso Rw Sw).hom.app K) =
      (mapDerivedCategoryCompIso (Rw ⋙ Sw) L).inv.app K := by
    rw [← Category.assoc, ha₂, Category.assoc, ← Functor.map_comp]
    simp
  simp only [mapDerivedCategoryTriangleIso, mapDerivedCategorySquareIso,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hd, hew]
  symm
  rw [reassoc_of% ha₁', reassoc_of% hβ', ← reassoc_of% hα,
    reassoc_of% ha₂']

section Conjugation
variable {P Q R S : Type*} [Category P] [Category Q] [Category R] [Category S]
    (SV : P ⥤ Q) (SW : R ⥤ S) (M : R ⥤ P) (L : S ⥤ Q)
    {Av Dv : P} {Aw Dw : R} {Aq Dq : Q} {As Ds : S}
    (δA : SV.obj Av ≅ Aq) (δD : SV.obj Dv ≅ Dq)
    (εA : SW.obj Aw ≅ As) (εD : SW.obj Dw ≅ Ds)
    (σA : Av ≅ M.obj Aw) (σD : Dv ≅ M.obj Dw)
    (cA : Aq ≅ L.obj As) (cD : Dq ≅ L.obj Ds)
    (α : M ⋙ SV ≅ SW ⋙ L)
    (hA : δA.hom ≫ cA.hom = SV.map σA.hom ≫ α.hom.app Aw ≫ L.map εA.hom)
    (hD : δD.hom ≫ cD.hom = SV.map σD.hom ≫ α.hom.app Dw ≫ L.map εD.hom)
include hA hD in
private theorem conjugation_natural (e : Aw ≅ Dw) :
    δA.symm ≪≫ SV.mapIso (σA ≪≫ M.mapIso e ≪≫ σD.symm) ≪≫ δD =
      cA ≪≫ L.mapIso (εA.symm ≪≫ SW.mapIso e ≪≫ εD) ≪≫ cD.symm := by
  apply Iso.ext
  apply (cancel_epi δA.hom).mp
  apply (cancel_mono cD.hom).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id]
  rw [hD]
  simp only [← SV.map_comp_assoc, Iso.inv_hom_id, SV.map_id, Category.id_comp]
  rw [SV.map_comp, Category.assoc]
  have hn := α.hom.naturality e.hom
  change SV.map (M.map e.hom) ≫ α.hom.app Dw =
    α.hom.app Aw ≫ L.map (SW.map e.hom) at hn
  rw [reassoc_of% hn]
  rw [reassoc_of% hA]
  simp only [← L.map_comp_assoc, Iso.hom_inv_id, L.map_id, Category.id_comp,
    Category.comp_id, Iso.hom_inv_id_assoc]
end Conjugation

end CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme
variable (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]

set_option backward.isDefEq.respectTransparency false in
noncomputable def etaleSliceRestrictionIso (V : X.Etale) :
    X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} B) V ⋙
      (Etale.overSheafEquiv V (ModuleCat.{u + 1} B)).functor ≅
        Etale.upperStar (ModuleCat.{u + 1} B) V.hom := by
  refine ?_ ≪≫ (Etale.upperStarIsoLocalizationRestriction
    (ModuleCat.{u + 1} B) V.hom V.prop).symm
  refine NatIso.ofComponents (fun F ↦ ?_) ?_
  · exact ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _))
  · intros
    ext
    rfl

instance etaleOverFunctor_additive (V : X.Etale) :
    (Etale.overSheafEquiv V (ModuleCat.{u + 1} B)).functor.Additive where
  map_add := by intros; rfl

instance etaleOverInverse_additive (V : X.Etale) :
    (Etale.overSheafEquiv V (ModuleCat.{u + 1} B)).inverse.Additive where
  map_add := by intros; rfl

noncomputable def etaleDerivedSliceEquivalence (V : X.Etale) :=
  (Etale.overSheafEquiv V (ModuleCat.{u + 1} B)).mapDerivedCategory

theorem etaleDerivedSliceEquivalence_functor (V : X.Etale) :
    (etaleDerivedSliceEquivalence X B V).functor =
      (Etale.overSheafEquiv V (ModuleCat.{u + 1} B)).functor.mapDerivedCategory := by
  rfl

noncomputable def etaleDerivedSliceRestrictionIso (V : X.Etale) :
    derivedSliceRestriction X.smallEtaleTopology B V ⋙
      (etaleDerivedSliceEquivalence X B V).functor ≅
        localIsomorphismRestriction X B V :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (etaleSliceRestrictionIso X B V)

noncomputable def etaleSourceToSliceIso
    (A K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (V : X.Etale)
    (e : (localIsomorphismRestriction X B V).obj A ≅
      (localIsomorphismRestriction X B V).obj K) :
    (derivedSliceRestriction X.smallEtaleTopology B V).obj A ≅
      (derivedSliceRestriction X.smallEtaleTopology B V).obj K :=
  (etaleDerivedSliceEquivalence X B V).functor.preimageIso
    ((etaleDerivedSliceRestrictionIso X B V).app A ≪≫ e ≪≫
      ((etaleDerivedSliceRestrictionIso X B V).app K).symm)

noncomputable def proetSliceEquivalence (U : X.ProEt) :=
  let := ProEt.sliceDense X U
  (ProEt.sliceEquiv X U).sheafCongr ((ProEt.topology X).over U)
    (ProEt.topology U.left) (ModuleCat.{u + 1} B)

instance proetSliceFunctor_additive (U : X.ProEt) :
    (proetSliceEquivalence X B U).functor.Additive where
  map_add := by intros; rfl

set_option backward.isDefEq.respectTransparency false in
noncomputable def proetSliceRestrictionIso (U : X.ProEt) :
    (ProEt.topology X).overPullback (ModuleCat.{u + 1} B) U ⋙
      (proetSliceEquivalence X B U).functor ≅
        ProEtale.upperStar (ModuleCat.{u + 1} B) U.hom := by
  refine ?_ ≪≫ (ProEtale.upperStarIsoLocalizationRestriction
    (ModuleCat.{u + 1} B) U.hom U.prop).symm
  exact NatIso.ofComponents
    (fun _ ↦ ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _)))

noncomputable def proetDerivedSliceRestrictionIso (U : X.ProEt) :
    derivedSliceRestriction (ProEt.topology X) B U ⋙
      (proetSliceEquivalence X B U).functor.mapDerivedCategory ≅
        (ProEtale.upperStar (ModuleCat.{u + 1} B) U.hom).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (proetSliceRestrictionIso X B U)

set_option backward.isDefEq.respectTransparency false in
noncomputable def etaleToOverMapIso {V W : X.Etale} (f : V ⟶ W) :
    Etale.etaleToOver V ⋙ Over.map f ≅
      MorphismProperty.Over.map ⊤ (show Etale f.left by infer_instance) ⋙
        Etale.etaleToOver W := by
  refine NatIso.ofComponents (fun T ↦ ?_) ?_
  · refine Over.isoMk (MorphismProperty.Over.isoMk (Iso.refl _) ?_) ?_
    · change 𝟙 T.left ≫ (T.hom ≫ f.left) ≫ W.hom = T.hom ≫ V.hom
      simp only [Category.id_comp, Category.assoc, MorphismProperty.Over.w]
    · apply MorphismProperty.Over.Hom.ext
      change 𝟙 T.left ≫ (T.hom ≫ f.left) = T.hom ≫ f.left
      exact Category.id_comp _
  · intro T T' g
    apply Over.OverMorphism.ext
    apply MorphismProperty.Over.Hom.ext
    exact (Category.comp_id _).trans (Category.id_comp _).symm

set_option backward.isDefEq.respectTransparency false in
noncomputable def etaleSliceMapIso {V W : X.Etale} (f : V ⟶ W) :
    X.smallEtaleTopology.overMapPullback (ModuleCat.{u + 1} B) f ⋙
      (Etale.overSheafEquiv V (ModuleCat.{u + 1} B)).functor ≅
        (Etale.overSheafEquiv W (ModuleCat.{u + 1} B)).functor ⋙
          Etale.upperStar (ModuleCat.{u + 1} B) f.left := by
  refine ?_ ≪≫ Functor.isoWhiskerLeft _
    (Etale.upperStarIsoLocalizationRestriction
      (ModuleCat.{u + 1} B) f.left
        (show Etale f.left by infer_instance)).symm
  refine NatIso.ofComponents (fun F ↦
    (fullyFaithfulSheafToPresheaf _ _).preimageIso
      (Functor.isoWhiskerRight (NatIso.op (etaleToOverMapIso X f).symm) F.obj)) ?_
  intro F G a
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext T
  exact (a.hom.naturality _).symm

set_option backward.isDefEq.respectTransparency false in
noncomputable def etaleDerivedSliceMapIso {V W : X.Etale} (f : V ⟶ W) :
    derivedSliceMap X.smallEtaleTopology B f ⋙
      (etaleDerivedSliceEquivalence X B V).functor ≅
        (etaleDerivedSliceEquivalence X B W).functor ⋙
          (Etale.upperStar (ModuleCat.{u + 1} B) f.left).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (etaleSliceMapIso X B f) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm

set_option backward.isDefEq.respectTransparency false in
noncomputable def etaleLocalizationCompIso {V W : X.Etale} (f : V ⟶ W) :
    Etale.localizationRestriction (ModuleCat.{u + 1} B) V.hom V.prop ≅
      Etale.localizationRestriction (ModuleCat.{u + 1} B) W.hom W.prop ⋙
      Etale.localizationRestriction (ModuleCat.{u + 1} B) f.left
        (show Etale f.left by infer_instance) :=
  Etale.localizationRestrictionComp' (ModuleCat.{u + 1} B) f.left W.hom V.hom f.w.symm

set_option backward.isDefEq.respectTransparency false in
theorem etaleSliceRestriction_comp_aux {V W : X.Etale} (f : V ⟶ W)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) :
    (etaleSliceRestrictionIso X B V).hom.app F ≫
      (Etale.upperStarIsoLocalizationRestriction
        (ModuleCat.{u + 1} B) V.hom V.prop).hom.app F ≫
      (etaleLocalizationCompIso X B f).hom.app F =
    (Etale.overSheafEquiv V (ModuleCat.{u + 1} B)).functor.map
      ((sliceRestrictionMapIso X.smallEtaleTopology B f).inv.app F) ≫
    (etaleSliceMapIso X B f).hom.app (F.over W) ≫
    (Etale.upperStar (ModuleCat.{u + 1} B) f.left).map
      ((etaleSliceRestrictionIso X B W).hom.app F) ≫
    (Etale.upperStar (ModuleCat.{u + 1} B) f.left).map
      ((Etale.upperStarIsoLocalizationRestriction
        (ModuleCat.{u + 1} B) W.hom W.prop).hom.app F) ≫
    (Etale.upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} B) f.left
      (show Etale f.left by infer_instance)).hom.app
      ((Etale.localizationRestriction (ModuleCat.{u + 1} B) W.hom W.prop).obj F) := by
  have hf := (Etale.upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} B) f.left
    (show Etale f.left by infer_instance)).hom.naturality
    ((etaleSliceRestrictionIso X B W).hom.app F ≫
      (Etale.upperStarIsoLocalizationRestriction
        (ModuleCat.{u + 1} B) W.hom W.prop).hom.app F)
  simp only [Functor.map_comp, Category.assoc] at hf
  rw [hf]
  simp only [etaleSliceRestrictionIso, etaleSliceMapIso, Iso.trans_hom,
    Iso.symm_hom, Iso.app_inv, Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc]
  dsimp only [Functor.comp_obj]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id, Category.comp_id]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext T
  dsimp only [Functor.comp_obj, NatTrans.comp_app,
    ObjectProperty.FullSubcategory.comp_hom, NatIso.ofComponents_hom_app,
    ObjectProperty.isoMk_hom, ObjectProperty.homMk_hom, Iso.refl_hom]
  simp only [ObjectProperty.isoMk_hom, NatIso.ofComponents_hom_app, Iso.refl_hom,
    Category.id_comp, Category.comp_id]
  dsimp only [ObjectProperty.homMk_hom, NatIso.ofComponents_hom_app, Iso.refl_hom,
    etaleLocalizationCompIso]
  simp only [Category.id_comp]
  change F.obj.map _ = (𝟙 _) ≫ F.obj.map _ ≫ (𝟙 _)
  simp only [Category.id_comp, Category.comp_id]
  congr 1

set_option backward.isDefEq.respectTransparency false in
theorem etaleSliceRestriction_comp {V W : X.Etale} (f : V ⟶ W)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) :
    (etaleSliceRestrictionIso X B V).hom.app F ≫
      (Etale.upperStarComp (ModuleCat.{u + 1} B) f.left W.hom V.hom f.w.symm).hom.app F =
    (Etale.overSheafEquiv V (ModuleCat.{u + 1} B)).functor.map
      ((sliceRestrictionMapIso X.smallEtaleTopology B f).inv.app F) ≫
    (etaleSliceMapIso X B f).hom.app (F.over W) ≫
    (Etale.upperStar (ModuleCat.{u + 1} B) f.left).map
      ((etaleSliceRestrictionIso X B W).hom.app F) := by
  apply (cancel_mono
    ((Etale.upperStar (ModuleCat.{u + 1} B) f.left).map
      ((Etale.upperStarIsoLocalizationRestriction
        (ModuleCat.{u + 1} B) W.hom W.prop).hom.app F) ≫
      (Etale.upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} B) f.left
        (show Etale f.left by infer_instance)).hom.app
          ((Etale.localizationRestriction (ModuleCat.{u + 1} B) W.hom W.prop).obj F))).mp
  simp only [Category.assoc]
  rw [← Etale.upperStarIsoLocalizationRestriction_comp]
  exact etaleSliceRestriction_comp_aux X B f F

set_option backward.isDefEq.respectTransparency false in
theorem etaleDerivedSliceRestriction_comp {V W : X.Etale} (f : V ⟶ W)
    (F : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    (etaleDerivedSliceRestrictionIso X B V).hom.app F ≫
      (localIsomorphismRestrictionComp X B f).hom.app F =
    (etaleDerivedSliceEquivalence X B V).functor.map
      ((derivedSliceMapIso X.smallEtaleTopology B f).inv.app F) ≫
    (etaleDerivedSliceMapIso X B f).hom.app
      ((derivedSliceRestriction X.smallEtaleTopology B W).obj F) ≫
    (Etale.upperStar (ModuleCat.{u + 1} B) f.left).mapDerivedCategory.map
      ((etaleDerivedSliceRestrictionIso X B W).hom.app F) := by
  have h := Functor.derived_path_coherence
    (X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} B) V)
    (Etale.overSheafEquiv V (ModuleCat.{u + 1} B)).functor
    (Etale.upperStar (ModuleCat.{u + 1} B) V.hom)
    (X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} B) W)
    (Etale.overSheafEquiv W (ModuleCat.{u + 1} B)).functor
    (Etale.upperStar (ModuleCat.{u + 1} B) W.hom)
    (X.smallEtaleTopology.overMapPullback (ModuleCat.{u + 1} B) f)
    (Etale.upperStar (ModuleCat.{u + 1} B) f.left)
    (etaleSliceRestrictionIso X B V) (etaleSliceRestrictionIso X B W)
    (sliceRestrictionMapIso X.smallEtaleTopology B f).symm
    (etaleSliceMapIso X B f)
    (Etale.upperStarComp (ModuleCat.{u + 1} B) f.left W.hom V.hom f.w.symm)
    (etaleSliceRestriction_comp X B f) F
  simp only [etaleDerivedSliceRestrictionIso, etaleDerivedSliceMapIso,
    localIsomorphismRestrictionComp, derivedSliceMapIso,
    etaleDerivedSliceEquivalence_functor,
    Functor.mapDerivedCategoryTriangleIso, Functor.mapDerivedCategorySquareIso,
    Functor.mapDerivedCategoryNatIso_symm, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app] at h ⊢
  convert! h using 1

noncomputable def etaleSliceToSourceIso
    (A D : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (V : X.Etale)
    (e : (derivedSliceRestriction X.smallEtaleTopology B V).obj A ≅
      (derivedSliceRestriction X.smallEtaleTopology B V).obj D) :
    (localIsomorphismRestriction X B V).obj A ≅
      (localIsomorphismRestriction X B V).obj D :=
  ((etaleDerivedSliceRestrictionIso X B V).app A).symm ≪≫
    (etaleDerivedSliceEquivalence X B V).functor.mapIso e ≪≫
      (etaleDerivedSliceRestrictionIso X B V).app D

set_option backward.isDefEq.respectTransparency false in
theorem etaleSliceToSourceIso_natural
    (A D : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    {V W : X.Etale} (f : V ⟶ W)
    (e : (derivedSliceRestriction X.smallEtaleTopology B W).obj A ≅
      (derivedSliceRestriction X.smallEtaleTopology B W).obj D) :
    etaleSliceToSourceIso X B A D V
      (derivedLocalIsoRestriction X.smallEtaleTopology B A D f e) =
    localIsomorphismMap A D f (etaleSliceToSourceIso X B A D W e) := by
  exact Functor.conjugation_natural
    (etaleDerivedSliceEquivalence X B V).functor
    (etaleDerivedSliceEquivalence X B W).functor
    (derivedSliceMap X.smallEtaleTopology B f)
    (Etale.upperStar (ModuleCat.{u + 1} B) f.left).mapDerivedCategory
    ((etaleDerivedSliceRestrictionIso X B V).app A)
    ((etaleDerivedSliceRestrictionIso X B V).app D)
    ((etaleDerivedSliceRestrictionIso X B W).app A)
    ((etaleDerivedSliceRestrictionIso X B W).app D)
    ((derivedSliceMapIso X.smallEtaleTopology B f).app A).symm
    ((derivedSliceMapIso X.smallEtaleTopology B f).app D).symm
    ((localIsomorphismRestrictionComp X B f).app A)
    ((localIsomorphismRestrictionComp X B f).app D)
    (etaleDerivedSliceMapIso X B f)
    (etaleDerivedSliceRestriction_comp X B f A)
    (etaleDerivedSliceRestriction_comp X B f D) e

set_option backward.isDefEq.respectTransparency false in
/-- The slice and source versions of the local Isom presheaf are naturally isomorphic.
The restriction compatibility follows from the localization composition isomorphisms.
Source: Stacks Tag 09BV
(blueprint: def-weil-pbc-source-derived-isomorphism-evaluation). -/
noncomputable def etaleIsomorphismPresheafIso
    (A D : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    derivedLocalIsoPresheaf X.smallEtaleTopology B A D ≅
      derivedLocalIsomorphismPresheaf A D := by
  refine NatIso.ofComponents (fun V ↦ ?_) ?_
  · exact
      { hom := TypeCat.ofHom (etaleSliceToSourceIso X B A D V.unop)
        inv := TypeCat.ofHom (etaleSourceToSliceIso X B A D V.unop)
        hom_inv_id := by
          apply ConcreteCategory.hom_ext
          intro e
          apply Iso.ext
          apply (etaleDerivedSliceEquivalence X B V.unop).functor.map_injective
          simp [etaleSliceToSourceIso, etaleSourceToSliceIso]
        inv_hom_id := by
          apply ConcreteCategory.hom_ext
          intro e
          apply Iso.ext
          simp [etaleSliceToSourceIso, etaleSourceToSliceIso] }
  · intro V W f
    apply ConcreteCategory.hom_ext
    intro e
    exact etaleSliceToSourceIso_natural X B A D f.unop e

/-- Sheafification of the canonical slice-to-source Isom-presheaf isomorphism.
Source: Stacks Tag 09BV
(blueprint: def-weil-pbc-source-derived-isomorphism-evaluation). -/
noncomputable def etaleIsomorphismSheafIso
    (A D : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    derivedLocalIsoSheaf X.smallEtaleTopology B A D ≅
      derivedLocalIsomorphismSheaf A D :=
  (presheafToSheaf X.smallEtaleTopology (Type (u + 1))).mapIso
    (etaleIsomorphismPresheafIso X B A D)

set_option backward.isDefEq.respectTransparency false in
/-- Evaluate source-site Isom-sheaf sections using slice localization and the unique
inverse of the pro-etale sheafification unit on a weakly contractible affine.
Source: Stacks Tags 09BV and 0F63
(blueprint: def-weil-pbc-source-derived-isomorphism-evaluation). -/
noncomputable def sourceDerivedIsoEvaluation
    (A D : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (U : X.ProEt) (ha : IsAffine U.left)
    (hU : (ProEt.topology X).IsWeaklyContractible.{u + 1} U)
    (s : ((comparisonSetUpperStar X).obj
      (derivedLocalIsomorphismSheaf A D)).obj.obj (op U)) :
    (localProEtaleComparison U.hom B).obj A ≅
      (localProEtaleComparison U.hom B).obj D := by
  letI := ha
  exact
    ((proetDerivedSliceRestrictionIso X B U).app ((derivedComparison X B).obj A)).symm ≪≫
    (proetSliceEquivalence X B U).functor.mapDerivedCategory.mapIso
      (derivedIsoEvaluation X B A D U hU
        (((comparisonSetUpperStar X).map
          (etaleIsomorphismSheafIso X B A D).inv).hom.app (op U) s)) ≪≫
    (proetDerivedSliceRestrictionIso X B U).app ((derivedComparison X B).obj D)

end AlgebraicGeometry.Scheme
