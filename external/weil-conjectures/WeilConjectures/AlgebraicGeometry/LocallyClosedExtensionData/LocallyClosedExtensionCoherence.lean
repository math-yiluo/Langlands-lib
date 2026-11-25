/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalPullbackComposition
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicFiniteOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.AlgebraicGeometry.LocallyClosedExtensionData.LocallyClosedModuleExtensionCoherence

import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.CategoryTheory.Localization.Adjunction
import Mathlib.CategoryTheory.Monad.Adjunction

/-!
# Normalized locally closed extensions with arbitrary pro-etale coefficients

The structures below package the witnesses in this single coherence assertion.
They do not choose a functor from a mere existence theorem. The only categories and
inverse/direct images used are the module-sheaf constructions. An open
extension is specified by its adjunction, equivalently by slice extension followed
by module sheafification. Closed extensions are identified with actual direct image.
All derived functors are the exact termwise localizations of these same functors.

## References

* Stacks Project, Tags 09AA, 09BM, 09BN and 09AH
* Tags 03DI and 03DJ
* Tag 02V0
-/

@[expose] public noncomputable section

set_option linter.privateModule false
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

namespace LocallyClosedExtensionData

end LocallyClosedExtensionData

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restriction_hom_bijective
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D) (G : D ⥤ C)
    [F.Full] [F.Faithful] (r : F ⋙ G ≅ 𝟭 C) (M N : C) :
    Function.Bijective (fun f : F.obj M ⟶ F.obj N ↦
      r.inv.app M ≫ G.map f ≫ r.hom.app N) := by
  have hr (f : M ⟶ N) :
      r.inv.app M ≫ G.map (F.map f) ≫ r.hom.app N = f := by
    simpa using congrArg (fun g ↦ r.inv.app M ≫ g) (r.hom.naturality f)
  constructor
  · intro f g h
    obtain ⟨f, rfl⟩ := F.map_surjective f
    obtain ⟨g, rfl⟩ := F.map_surjective g
    change r.inv.app M ≫ G.map (F.map f) ≫ r.hom.app N =
      r.inv.app M ≫ G.map (F.map g) ≫ r.hom.app N at h
    rw [hr, hr] at h
    exact congrArg F.map h
  · intro f
    exact ⟨F.map f, hr f⟩

private noncomputable def exactAdjunction
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (adj : F ⊣ G) :
    F.mapDerivedCategory ⊣ G.mapDerivedCategory := by
  let : CatCommSq (F.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q F.mapDerivedCategory := ⟨F.mapDerivedCategoryFactors.symm⟩
  let : CatCommSq (G.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q G.mapDerivedCategory := ⟨G.mapDerivedCategoryFactors.symm⟩
  exact (adj.mapHomologicalComplex (.up ℤ)).localization DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ)) DerivedCategory.Q
    (HomologicalComplex.quasiIso D (.up ℤ)) F.mapDerivedCategory G.mapDerivedCategory

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derived_postcompose
    {C D B : Type*} [Category C] [Category D] [Category B]
    [Abelian C] [Abelian D] [Abelian B]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory B]
    {F : C ⥤ D} {G : D ⥤ B} {H H' : C ⥤ B}
    [F.Additive] [G.Additive] [H.Additive] [H'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits H'] [PreservesFiniteColimits H']
    (γ : F ⋙ G ≅ H) (e : H ≅ H') :
    Functor.mapDerivedCategoryCompNatIso (γ ≪≫ e) =
      Functor.mapDerivedCategoryCompNatIso γ ≪≫ Functor.mapDerivedCategoryNatIso e := by
  apply Iso.ext
  simp only [Functor.mapDerivedCategoryCompNatIso, Iso.trans_hom,
    Functor.mapDerivedCategoryNatIso_trans, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derived_eqToIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {A : Type*} (F : A → C ⥤ D) [∀ a, (F a).Additive]
    [∀ a, PreservesFiniteLimits (F a)] [∀ a, PreservesFiniteColimits (F a)]
    {a b : A} (h : a = b) :
    Functor.mapDerivedCategoryNatIso (eqToIso (congrArg F h)) =
      eqToIso (congrArg (fun x ↦ (F x).mapDerivedCategory) h) := by
  subst b
  apply Iso.ext
  exact Functor.mapDerivedCategoryNatIso_refl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derived_left_unit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (I : C ⥤ C) (F : C ⥤ D) [I.Additive] [F.Additive]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (e : I ≅ 𝟭 C) :
    Functor.mapDerivedCategoryCompNatIso
        (Functor.isoWhiskerRight e F ≪≫ Functor.leftUnitor F) =
      Functor.isoWhiskerRight
        (Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso C)
        F.mapDerivedCategory ≪≫ Functor.leftUnitor F.mapDerivedCategory := by
  apply Iso.ext
  rw [derived_postcompose]
  have hL : (Functor.mapDerivedCategoryNatIso (Functor.leftUnitor F)).hom = 𝟙 _ :=
    Functor.mapDerivedCategoryNatIso_refl
  ext K
  simp only [Iso.trans_hom, NatTrans.comp_app, hL, Functor.comp_obj,
    Functor.id_obj, Category.comp_id,
    Functor.mapDerivedCategoryCompNatIso, Functor.isoWhiskerRight_hom,
    Functor.leftUnitor_hom_app, Functor.whiskerRight_app, CategoryTheory.Functor.map_comp]
  rw [← cancel_epi ((Functor.mapDerivedCategoryCompIso I F).inv.app K),
    Iso.inv_hom_id_app_assoc]
  have hn := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerRight e F) K
  have hu := congr_app (Functor.mapDerivedCategoryCompIso_id_comp F) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, NatTrans.id_app] at hn hu
  simp only [Functor.comp_obj, Functor.id_obj] at hn hu ⊢
  rw [← Category.assoc, ← hn, Category.assoc, hu]
  exact (Category.comp_id _).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derived_right_unit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (I : D ⥤ D) (F : C ⥤ D) [I.Additive] [F.Additive]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (e : I ≅ 𝟭 D) :
    Functor.mapDerivedCategoryCompNatIso
        (Functor.isoWhiskerLeft F e ≪≫ Functor.rightUnitor F) =
      Functor.isoWhiskerLeft F.mapDerivedCategory
        (Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso D) ≪≫
          Functor.rightUnitor F.mapDerivedCategory := by
  apply Iso.ext
  rw [derived_postcompose]
  have hL : (Functor.mapDerivedCategoryNatIso (Functor.rightUnitor F)).hom = 𝟙 _ :=
    Functor.mapDerivedCategoryNatIso_refl
  ext K
  simp only [Iso.trans_hom, NatTrans.comp_app, hL, Functor.comp_obj,
    Functor.id_obj, Category.comp_id,
    Functor.mapDerivedCategoryCompNatIso, Functor.isoWhiskerLeft_hom,
    Functor.rightUnitor_hom_app, Functor.whiskerLeft_app]
  rw [← cancel_epi ((Functor.mapDerivedCategoryCompIso F I).inv.app K),
    Iso.inv_hom_id_app_assoc]
  have hn := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft F e) K
  have hu := congr_app (Functor.mapDerivedCategoryCompIso_comp_id F) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, NatTrans.id_app] at hn hu
  simp only [Functor.comp_obj, Functor.id_obj] at hn hu ⊢
  rw [← Category.assoc, ← hn, Category.assoc, hu]
  exact (Category.comp_id _).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derived_cocycle
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F : A ⥤ B} {G : B ⥤ C} {H : C ⥤ D}
    {FG : A ⥤ C} {GH : B ⥤ D} {FGH : A ⥤ D}
    [F.Additive] [G.Additive] [H.Additive] [FG.Additive] [GH.Additive] [FGH.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits FG] [PreservesFiniteColimits FG]
    [PreservesFiniteLimits GH] [PreservesFiniteColimits GH]
    [PreservesFiniteLimits FGH] [PreservesFiniteColimits FGH]
    (eFG : F ⋙ G ≅ FG) (eFGH : FG ⋙ H ≅ FGH)
    (eGH : G ⋙ H ≅ GH) (eFGH' : F ⋙ GH ≅ FGH)
    (h : Functor.isoWhiskerRight eFG H ≪≫ eFGH =
      Functor.associator F G H ≪≫ Functor.isoWhiskerLeft F eGH ≪≫ eFGH') :
    Functor.isoWhiskerRight (Functor.mapDerivedCategoryCompNatIso eFG)
        H.mapDerivedCategory ≪≫ Functor.mapDerivedCategoryCompNatIso eFGH =
      Functor.associator F.mapDerivedCategory G.mapDerivedCategory H.mapDerivedCategory ≪≫
        Functor.isoWhiskerLeft F.mapDerivedCategory
          (Functor.mapDerivedCategoryCompNatIso eGH) ≪≫
            Functor.mapDerivedCategoryCompNatIso eFGH' := by
  have hm (M : A) := congr_app (congrArg Iso.hom h) M
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp] at hm
  apply Iso.ext
  ext K
  simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp] using
      Functor.mapDerivedCategoryCompNatIso_cocycle eFG eFGH eGH eFGH' hm K

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem identity_factors {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (K : CochainComplex C ℤ) :
    (Functor.mapDerivedCategoryIdIso C).hom.app (DerivedCategory.Q.obj K) =
      (𝟭 C).mapDerivedCategoryFactors.hom.app K := by
  rw [Functor.mapDerivedCategoryIdIso_hom_app]
  have h : (Functor.mapHomologicalComplexIdIso C (.up ℤ)).hom.app K = 𝟙 _ := rfl
  rw [h]
  erw [DerivedCategory.Q.map_id, Category.comp_id]

namespace LocallyClosedExtensionData

private noncomputable def derivedRestriction (E : LocallyClosedExtensionData.{u})
    {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X) :
    E.derived a ⋙ a.pull.mapDerivedCategory ≅ 𝟭 _ :=
  (Functor.mapDerivedCategoryCompNatIso (E.restriction a)) ≪≫
    Functor.mapDerivedCategoryIdIso _

private noncomputable def derivedGamma (E : LocallyClosedExtensionData.{u})
    {S X T : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X)
    (b : LocallyClosedCoefficientImmersion T S) :
    E.derived b ⋙ E.derived a ≅ E.derived (a.comp b) :=
  Functor.mapDerivedCategoryCompNatIso (E.gamma a b)

private noncomputable def derivedIdentity (E : LocallyClosedExtensionData.{u})
    (X : LocallyClosedCoefficients.{u}) : E.derived (.identity X) ≅ 𝟭 _ :=
  Functor.mapDerivedCategoryNatIso (E.identity X) ≪≫ Functor.mapDerivedCategoryIdIso _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem identityTermwise (E : LocallyClosedExtensionData.{u})
    (X : LocallyClosedCoefficients.{u})
    (K : CochainComplex (proEtaleRingModules X.scheme X.ring) ℤ) :
    (E.derivedIdentity X).hom.app (DerivedCategory.Q.obj K) =
      (E.extension (.identity X)).mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (E.identity X) (.up ℤ)).hom.app K) := by
  have h := Functor.mapDerivedCategoryNatIso_fac (E.identity X) K
  change (Functor.mapDerivedCategoryNatIso (E.identity X)).hom.app _ ≫ _ = _ at h
  dsimp only [derivedIdentity, Iso.trans_hom, NatTrans.comp_app]
  rw [identity_factors]
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restrictionTermwise (E : LocallyClosedExtensionData.{u})
    {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X)
    (K : CochainComplex (proEtaleRingModules S.scheme S.ring) ℤ) :
    (E.derivedRestriction a).hom.app (DerivedCategory.Q.obj K) =
      a.pull.mapDerivedCategory.map ((E.extension a).mapDerivedCategoryFactors.hom.app K) ≫
        a.pull.mapDerivedCategoryFactors.hom.app
          (((E.extension a).mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (E.restriction a) (.up ℤ)).hom.app K) := by
  have h := Functor.mapDerivedCategoryCompNatIso_hom_app_Q (E.restriction a) K
  dsimp only [Functor.mapHomologicalComplexCompIsoHomOfIso] at h
  rw [Functor.mapHomologicalComplexCompIso_refl_hom_app] at h
  erw [Category.id_comp] at h
  dsimp only [derivedRestriction, Iso.trans_hom, NatTrans.comp_app]
  rw [identity_factors]
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem gammaTermwise (E : LocallyClosedExtensionData.{u})
    {S X T : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X)
    (b : LocallyClosedCoefficientImmersion T S)
    (K : CochainComplex (proEtaleRingModules T.scheme T.ring) ℤ) :
    (E.derivedGamma a b).hom.app (DerivedCategory.Q.obj K) ≫
        (E.extension (a.comp b)).mapDerivedCategoryFactors.hom.app K =
      (E.derived a).map ((E.extension b).mapDerivedCategoryFactors.hom.app K) ≫
        (E.extension a).mapDerivedCategoryFactors.hom.app
          (((E.extension b).mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (E.gamma a b) (.up ℤ)).hom.app K) := by
  have h := Functor.mapDerivedCategoryCompNatIso_hom_app_Q (E.gamma a b) K
  dsimp only [Functor.mapHomologicalComplexCompIsoHomOfIso] at h
  rw [Functor.mapHomologicalComplexCompIso_refl_hom_app] at h
  erw [Category.id_comp] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derived_associative (E : LocallyClosedExtensionData.{u}) (hE : E.Coherent)
    {S X T W : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X)
    (b : LocallyClosedCoefficientImmersion T S) (d : LocallyClosedCoefficientImmersion W T) :
    ∃ h : (a.comp b).comp d = a.comp (b.comp d),
      Functor.isoWhiskerRight (E.derivedGamma b d) (E.derived a) ≪≫
          E.derivedGamma a (b.comp d) =
        Functor.associator (E.derived d) (E.derived b) (E.derived a) ≪≫
          Functor.isoWhiskerLeft (E.derived d) (E.derivedGamma a b) ≪≫
            E.derivedGamma (a.comp b) d ≪≫ eqToIso (congrArg E.derived h) := by
  obtain ⟨h, hh⟩ := hE.associative a b d
  refine ⟨h, ?_⟩
  have hc := derived_cocycle (E.gamma b d) (E.gamma a (b.comp d))
    (E.gamma a b) (E.gamma (a.comp b) d ≪≫ eqToIso (congrArg E.extension h)) hh
  rw [derived_postcompose, derived_eqToIso E.extension h] at hc
  exact hc

end LocallyClosedExtensionData

end AlgebraicGeometry.Scheme
