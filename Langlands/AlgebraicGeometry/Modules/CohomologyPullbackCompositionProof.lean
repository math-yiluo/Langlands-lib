import Langlands.AlgebraicGeometry.Modules.CohomologyPullbackCoefficientNaturalityProof

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry
open Langlands.Cohomology

namespace Langlands.Cohomology.DerivedPlus

section AcyclicComparison

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [Abelian D] [EnoughInjectives C]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (H : C ⥤ D) [H.Additive]
  (U : CochainComplex.Plus C ⥤ E)
  (V : DerivedCategory.Plus D ⥤ E)

set_option backward.isDefEq.respectTransparency false in
lemma exists_acyclicComparison
    (γ : H.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⋙ V ⟶ U)
    (hγ : ∀ (K : CochainComplex.Plus (InjectiveObject C)),
      IsIso (γ.app ((InjectiveObject.ι C).mapCochainComplexPlus.obj K))) :
    ∃ (β : U ⟶ DerivedCategory.Plus.Q ⋙ H.rightDerivedFunctorPlus ⋙ V),
      γ ≫ β = whiskerRight H.rightDerivedFunctorPlusUnit V := by
  let Φ := CochainComplex.Plus.localizerMorphism C
  let Q := DerivedCategory.Plus.Q (C := C)
  let W := CochainComplex.Plus.quasiIso C
  let T := H.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⋙ V
  let RT := H.rightDerivedFunctorPlus ⋙ V
  let α : T ⟶ Q ⋙ RT := whiskerRight H.rightDerivedFunctorPlusUnit V
  have hT : Φ.Derives T :=
    MorphismProperty.IsInvertedBy.of_comp _
      (Φ.functor ⋙ H.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q)
      (CochainComplex.Plus.localizerMorphism_derives_mapCochainComplexPlus H) V
  have : IsIso (whiskerLeft Φ.functor γ) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact hγ
  have hU : Φ.Derives U :=
    (MorphismProperty.IsInvertedBy.iff_of_iso _ (asIso (whiskerLeft Φ.functor γ))).1 hT
  have := hU.hasPointwiseRightDerivedFunctor
  have hα (K : CochainComplex.Plus (InjectiveObject C)) :
      IsIso (α.app (Φ.functor.obj K)) := by
    dsimp [α, Φ]
    infer_instance
  have : RT.IsRightDerivedFunctor α W := hT.isRightDerivedFunctor_of_isIso α hα
  let RU := U.totalRightDerived Q W
  let ε := U.totalRightDerivedUnit Q W
  let δ : RT ⟶ RU := Functor.rightDerivedNatTrans RT RU α ε W γ
  have hδ (K : CochainComplex.Plus (InjectiveObject C)) :
      IsIso (δ.app (Q.obj (Φ.functor.obj K))) := by
    have := hα K
    have : IsIso (γ.app (Φ.functor.obj K)) := hγ K
    have := hU.isIso_of_isRightDerivedFunctor ε K
    rw [← isIso_comp_left_iff (α.app (Φ.functor.obj K))]
    rw [Functor.rightDerivedNatTrans_app]
    infer_instance
  have : IsIso δ := by
    have := Φ.essSurj_of_hasRightResolutions Q
    rw [NatTrans.isIso_iff_isIso_app]
    intro Y
    rw [NatTrans.isIso_app_iff_of_iso δ ((Φ.functor ⋙ Q).objObjPreimageIso Y).symm]
    exact hδ _
  refine ⟨ε ≫ whiskerLeft Q (inv δ), ?_⟩
  rw [← Category.assoc, ← Functor.rightDerivedNatTrans_fac RT RU α ε W γ]
  rw [Category.assoc, ← whiskerLeft_comp]
  change α ≫ whiskerLeft Q (δ ≫ inv δ) = α
  simp only [IsIso.hom_inv_id, whiskerLeft_id', Category.comp_id]

end AcyclicComparison

section ComparisonExt

variable {C E : Type*} [Category* C] [Category* E]
  [Abelian C] [EnoughInjectives C] [HasDerivedCategory C]

set_option backward.isDefEq.respectTransparency false in
lemma natTrans_ext_on_injective_complexes
    {U : CochainComplex.Plus C ⥤ E} {V : DerivedCategory.Plus C ⥤ E}
    (α β : U ⟶ DerivedCategory.Plus.Q ⋙ V)
    (h : ∀ K : CochainComplex.Plus (InjectiveObject C),
      α.app ((InjectiveObject.ι C).mapCochainComplexPlus.obj K) =
        β.app ((InjectiveObject.ι C).mapCochainComplexPlus.obj K)) :
    α = β := by
  ext K
  let I : (CochainComplex.Plus.localizerMorphism C).RightResolution K :=
    Classical.arbitrary _
  have : IsIso (DerivedCategory.Plus.Q.map I.w) :=
    Localization.inverts DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso C) I.w I.hw
  have : IsIso ((DerivedCategory.Plus.Q ⋙ V).map I.w) := by
    dsimp
    infer_instance
  apply (cancel_mono ((DerivedCategory.Plus.Q ⋙ V).map I.w)).1
  rw [← α.naturality, ← β.naturality]
  exact congrArg (fun f => U.map I.w ≫ f) (h I.X₁)

end ComparisonExt

section MapPlusComp

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroMorphisms E]
  {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E}
  [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] [H.PreservesZeroMorphisms]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
def mapCochainComplexPlusCompIso (e : F ⋙ G ≅ H) :
    F.mapCochainComplexPlus ⋙ G.mapCochainComplexPlus ≅ H.mapCochainComplexPlus :=
  NatIso.ofComponents (fun K => (CochainComplex.Plus.ι E).preimageIso
    ((Functor.mapHomologicalComplexCompIso e _).app K.obj)) (fun f => by
      apply (CochainComplex.Plus.ι E).map_injective
      simp only [Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage]
      ext i
      exact e.hom.naturality (f.hom.f i))

end MapPlusComp

section SinglePlus

variable (C : Type*) [Category* C] [Abelian C]

/-- The complex with one object in degree zero, regarded as bounded below. -/
abbrev singlePlusFunctor : C ⥤ CochainComplex.Plus C :=
  ObjectProperty.lift _ (CochainComplex.singleFunctor C 0)
    (fun _ => ⟨0, inferInstance⟩)

variable [HasDerivedCategory C]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
def singlePlusQIso : DerivedCategory.Plus.singleFunctor C 0 ≅
    singlePlusFunctor C ⋙ DerivedCategory.Plus.Q :=
  NatIso.ofComponents (fun A => DerivedCategory.Plus.ι.preimageIso
    ((DerivedCategory.Plus.singleFunctorιIso C 0).app A ≪≫
      (DerivedCategory.singleFunctorIsoCompQ C 0).app A ≪≫
      ((DerivedCategory.Plus.QCompιIso C).app ((singlePlusFunctor C).obj A)).symm))
    (fun {A B} f => by
      apply DerivedCategory.Plus.ι.map_injective
      have h₁ := (DerivedCategory.Plus.singleFunctorιIso C 0).hom.naturality f
      have h₂ := (DerivedCategory.singleFunctorIsoCompQ C 0).hom.naturality f
      have h₃ := (DerivedCategory.Plus.QCompιIso C).inv.naturality
        ((singlePlusFunctor C).map f)
      simp only [Functor.comp_map] at h₁ h₂ h₃
      simp only [Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage,
        Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Category.assoc]
      rw [reassoc_of% h₁, reassoc_of% h₂]
      exact congrArg (fun g => (DerivedCategory.Plus.singleFunctorιIso C 0).hom.app A ≫
        (DerivedCategory.singleFunctorIsoCompQ C 0).hom.app A ≫ g) h₃)

variable {C} {D : Type*} [Category* D] [Abelian D] (F : C ⥤ D) [F.Additive]

set_option backward.isDefEq.respectTransparency false in
def singlePlusMapIso : F ⋙ singlePlusFunctor D ≅
    singlePlusFunctor C ⋙ F.mapCochainComplexPlus :=
  NatIso.ofComponents (fun A => (CochainComplex.Plus.ι D).preimageIso
    ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app A).symm)
    (fun f => by
      apply (CochainComplex.Plus.ι D).map_injective
      simp only [Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage,
        Iso.symm_hom]
      exact (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.naturality f)

variable [EnoughInjectives C]

/-- The augmentation of a resolution as a map of bounded below complexes. -/
abbrev resolutionPlusι {A : C} (I : InjectiveResolution A) :
    (singlePlusFunctor C).obj A ⟶ resolutionPlus I :=
  ObjectProperty.homMk I.ι'

instance {A : C} (I : InjectiveResolution A) :
    IsIso (DerivedCategory.Plus.Q.map (resolutionPlusι I)) := by
  apply Localization.inverts DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso C)
  change QuasiIso I.ι'
  infer_instance

omit [EnoughInjectives C] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma singleIsoOfResolution_hom_eq {A : C} (I : InjectiveResolution A) :
    (singleIsoOfResolution I).hom = (singlePlusQIso C).hom.app A ≫
      DerivedCategory.Plus.Q.map (resolutionPlusι I) := by
  apply DerivedCategory.Plus.ι.map_injective
  have h := (DerivedCategory.Plus.QCompιIso C).inv.naturality (resolutionPlusι I)
  simp only [Functor.comp_map] at h
  simp only [singleIsoOfResolution, singlePlusQIso, NatIso.ofComponents_hom_app,
    Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage, Iso.trans_hom,
    Iso.symm_hom, asIso_hom, Iso.app_hom, Iso.app_inv, Category.assoc]
  exact congrArg (fun f => (DerivedCategory.Plus.singleFunctorιIso C 0).hom.app A ≫
      (DerivedCategory.singleFunctorIsoCompQ C 0).hom.app A ≫ f) h

omit [HasDerivedCategory C] [EnoughInjectives C] in
lemma extendXIso_inv_comp_mapExtendIso_hom {ι ι' : Type*} {c : ComplexShape ι}
    {c' : ComplexShape ι'} (K : HomologicalComplex C c) (e : c.Embedding c')
    {i : ι} {i' : ι'} (hi : e.f i = i') :
    (((F.mapHomologicalComplex c).obj K).extendXIso e hi).inv ≫
        (mapExtendIso F K e).hom.f i' =
      F.map (K.extendXIso e hi).inv := by
  have aux (j : Option ι) (hj : j = some i) :
      (HomologicalComplex.extend.XIso ((F.mapHomologicalComplex c).obj K) hj).inv ≫
        (extendXMapIso F K j).hom =
      F.map (HomologicalComplex.extend.XIso K hj).inv := by
    subst hj
    dsimp [extendXMapIso, HomologicalComplex.extend.XIso, HomologicalComplex.extend.X]
    change 𝟙 (F.obj (K.X i)) ≫ 𝟙 _ = F.map (𝟙 (K.X i))
    simp
  exact aux _ (e.r_eq_some hi)

end SinglePlus

section SinglePlusComp

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E]
  {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E}
  [F.Additive] [G.Additive] [H.Additive]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma singlePlusMapIso_comp (e : F ⋙ G ≅ H) (A : C) :
    (singlePlusMapIso G).hom.app (F.obj A) ≫
        G.mapCochainComplexPlus.map ((singlePlusMapIso F).hom.app A) ≫
        (mapCochainComplexPlusCompIso e).hom.app ((singlePlusFunctor C).obj A) =
      (singlePlusFunctor E).map (e.hom.app A) ≫ (singlePlusMapIso H).hom.app A := by
  apply (CochainComplex.Plus.ι E).map_injective
  simp only [Functor.map_comp, singlePlusMapIso, mapCochainComplexPlusCompIso,
    NatIso.ofComponents_hom_app, Functor.preimageIso_hom, Functor.map_preimage,
    Iso.symm_hom]
  change (HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).inv.app (F.obj A) ≫
      (G.mapHomologicalComplex _).map
        ((CochainComplex.Plus.ι D).map ((singlePlusMapIso F).hom.app A)) ≫
      (Functor.mapHomologicalComplexCompIso e _).hom.app
        ((CochainComplex.singleFunctor C 0).obj A) =
    (CochainComplex.singleFunctor E 0).map (e.hom.app A) ≫
      (HomologicalComplex.singleMapHomologicalComplex H (.up ℤ) 0).inv.app A
  simp only [singlePlusMapIso, NatIso.ofComponents_hom_app,
    Functor.preimageIso_hom, Functor.map_preimage, Iso.symm_hom]
  apply HomologicalComplex.from_single_hom_ext
  simp only [HomologicalComplex.comp_f,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    Functor.mapHomologicalComplex_map_f,
    Functor.mapHomologicalComplexCompIso_hom_app_f, CochainComplex.singleFunctor,
    HomologicalComplex.single_map_f_self, Category.assoc]
  simp only [Iso.app_inv,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    Iso.inv_hom_id_assoc, ← Functor.map_comp_assoc]
  simpa only [Functor.comp_map, Functor.comp_obj,
    Functor.mapHomologicalComplex_obj_X] using congrArg
    (fun f => (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (G.obj (F.obj A))).hom ≫ f)
    (e.hom.naturality (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).inv)

end SinglePlusComp

end Langlands.Cohomology.DerivedPlus

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

attribute [local instance] HasDerivedCategory.standard

variable {R : CommRingCat.{u}} {X Y Z : Over (Spec R)}

def relativePushforwardSectionsComplexIso (h : Y ⟶ X) :
    (Scheme.Modules.pushforward h.left).mapCochainComplexPlus ⋙
        (relativeGlobalSections X.hom).mapCochainComplexPlus ≅
      (relativeGlobalSections Y.hom).mapCochainComplexPlus :=
  NatIso.ofComponents (pullbackSectionsComplexIso h)
    (fun ψ => pullbackSectionsComplexIso_hom_naturality h ψ)

abbrev pushforwardDerivedSectionsComplex (h : Y ⟶ X) :
    CochainComplex.Plus Y.left.Modules ⥤ DerivedCategory.Plus (ModuleCat.{u} R) :=
  (Scheme.Modules.pushforward h.left).mapCochainComplexPlus ⋙
    DerivedCategory.Plus.Q ⋙ (relativeGlobalSections X.hom).rightDerivedFunctorPlus

set_option backward.isDefEq.respectTransparency false in
lemma isIso_unit_pushforward_injective_complex (h : Y ⟶ X)
    (K : CochainComplex.Plus (InjectiveObject Y.left.Modules)) :
    IsIso ((relativeGlobalSections X.hom).rightDerivedFunctorPlusUnit.app
      ((Scheme.Modules.pushforward h.left).mapCochainComplexPlus.obj
        ((InjectiveObject.ι Y.left.Modules).mapCochainComplexPlus.obj K))) := by
  apply acyclicTermsDerivedUnitStatement
  intro i q
  exact (pushforwardInjectiveAcyclic Y.left X.left h.left
    (((InjectiveObject.ι Y.left.Modules).mapCochainComplexPlus.obj K).obj.X i)
    (K.obj.X i).property q).2 R X.hom

set_option backward.isDefEq.respectTransparency false in
lemma exists_pushforwardDerivedSectionsComparison (h : Y ⟶ X) :
    ∃ (β : pushforwardDerivedSectionsComplex h ⟶
        DerivedCategory.Plus.Q ⋙ (relativeGlobalSections Y.hom).rightDerivedFunctorPlus),
      ∀ K : CochainComplex.Plus Y.left.Modules,
        (relativeGlobalSections X.hom).rightDerivedFunctorPlusUnit.app
            ((Scheme.Modules.pushforward h.left).mapCochainComplexPlus.obj K) ≫ β.app K =
          DerivedCategory.Plus.Q.map (pullbackSectionsComplexIso h K).hom ≫
            (relativeGlobalSections Y.hom).rightDerivedFunctorPlusUnit.app K := by
  let γ : (relativeGlobalSections Y.hom).mapCochainComplexPlus ⋙
      DerivedCategory.Plus.Q ⋙ 𝟭 (DerivedCategory.Plus (ModuleCat.{u} R)) ⟶
      pushforwardDerivedSectionsComplex h :=
    whiskerRight (relativePushforwardSectionsComplexIso h).inv DerivedCategory.Plus.Q ≫
      whiskerLeft (Scheme.Modules.pushforward h.left).mapCochainComplexPlus
        (relativeGlobalSections X.hom).rightDerivedFunctorPlusUnit
  have hγ (K : CochainComplex.Plus (InjectiveObject Y.left.Modules)) :
      IsIso (γ.app ((InjectiveObject.ι Y.left.Modules).mapCochainComplexPlus.obj K)) := by
    have := isIso_unit_pushforward_injective_complex h K
    dsimp [γ]
    infer_instance
  obtain ⟨β, hβ⟩ := DerivedPlus.exists_acyclicComparison
    (relativeGlobalSections Y.hom) (pushforwardDerivedSectionsComplex h)
    (𝟭 (DerivedCategory.Plus (ModuleCat.{u} R))) γ hγ
  refine ⟨β, fun K => ?_⟩
  have H := NatTrans.congr_app hβ K
  change (DerivedCategory.Plus.Q.map (pullbackSectionsComplexIso h K).inv ≫
      (relativeGlobalSections X.hom).rightDerivedFunctorPlusUnit.app
        ((Scheme.Modules.pushforward h.left).mapCochainComplexPlus.obj K)) ≫ β.app K =
    (relativeGlobalSections Y.hom).rightDerivedFunctorPlusUnit.app K at H
  apply (cancel_epi (DerivedCategory.Plus.Q.map (pullbackSectionsComplexIso h K).inv)).1
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id, DerivedCategory.Plus.Q.map_id,
    Category.id_comp]
  simpa only [Category.assoc, Over.comp_left, Functor.comp_obj] using H

def pushforwardDerivedSectionsComparison (h : Y ⟶ X) :
    pushforwardDerivedSectionsComplex h ⟶
      DerivedCategory.Plus.Q ⋙ (relativeGlobalSections Y.hom).rightDerivedFunctorPlus :=
  Classical.choose (exists_pushforwardDerivedSectionsComparison h)

@[reassoc]
lemma pushforwardDerivedSectionsComparison_fac (h : Y ⟶ X)
    (K : CochainComplex.Plus Y.left.Modules) :
    (relativeGlobalSections X.hom).rightDerivedFunctorPlusUnit.app
        ((Scheme.Modules.pushforward h.left).mapCochainComplexPlus.obj K) ≫
      (pushforwardDerivedSectionsComparison h).app K =
    DerivedCategory.Plus.Q.map (pullbackSectionsComplexIso h K).hom ≫
      (relativeGlobalSections Y.hom).rightDerivedFunctorPlusUnit.app K :=
  Classical.choose_spec (exists_pushforwardDerivedSectionsComparison h) K

def pushforwardCompComplexIso (h : Y ⟶ X) (k : Z ⟶ Y) :
    (Scheme.Modules.pushforward k.left).mapCochainComplexPlus ⋙
        (Scheme.Modules.pushforward h.left).mapCochainComplexPlus ≅
      (Scheme.Modules.pushforward (k ≫ h).left).mapCochainComplexPlus :=
  DerivedPlus.mapCochainComplexPlusCompIso (Scheme.Modules.pushforwardComp k.left h.left)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma pullbackComposition_sections (h : Y ⟶ X) (k : Z ⟶ Y) (M : Z.left.Modules) :
    (relativeGlobalSections X.hom).map
        ((Scheme.Modules.pushforwardComp k.left h.left).hom.app M) ≫
      (relativePushforwardSectionsIso (k ≫ h)).hom.app M =
    (relativePushforwardSectionsIso h).hom.app ((Scheme.Modules.pushforward k.left).obj M) ≫
      (relativePushforwardSectionsIso k).hom.app M := by
  change moduleSpecΓFunctor.map
      ((Scheme.Modules.pushforward X.hom).map
        ((Scheme.Modules.pushforwardComp k.left h.left).hom.app M)) ≫
      (moduleSpecΓFunctor.map
        ((Scheme.Modules.pushforwardComp (k ≫ h).left X.hom).hom.app M) ≫
      moduleSpecΓFunctor.map
        ((Scheme.Modules.pushforwardCongr (k ≫ h).w).hom.app M)) =
    (moduleSpecΓFunctor.map
        ((Scheme.Modules.pushforwardComp h.left X.hom).hom.app
          ((Scheme.Modules.pushforward k.left).obj M)) ≫
      moduleSpecΓFunctor.map
        ((Scheme.Modules.pushforwardCongr h.w).hom.app
          ((Scheme.Modules.pushforward k.left).obj M))) ≫
    (moduleSpecΓFunctor.map
        ((Scheme.Modules.pushforwardComp k.left Y.hom).hom.app M) ≫
      moduleSpecΓFunctor.map
        ((Scheme.Modules.pushforwardCongr k.w).hom.app M))
  simp only [← Functor.map_comp, Category.assoc]
  congr 1
  apply Scheme.Modules.hom_ext
  intro U
  simp
  change M.presheaf.map _ = M.presheaf.map _ ≫ M.presheaf.map _
  rw [← M.presheaf.map_comp]
  congr 1

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma pullbackComposition_sectionsComplex (h : Y ⟶ X) (k : Z ⟶ Y)
    (K : CochainComplex.Plus Z.left.Modules) :
    (relativeGlobalSections X.hom).mapCochainComplexPlus.map
        ((pushforwardCompComplexIso h k).hom.app K) ≫
      (pullbackSectionsComplexIso (k ≫ h) K).hom =
    (pullbackSectionsComplexIso h
        ((Scheme.Modules.pushforward k.left).mapCochainComplexPlus.obj K)).hom ≫
      (pullbackSectionsComplexIso k K).hom := by
  apply (CochainComplex.Plus.ι _).map_injective
  simp only [Functor.map_comp, pullbackSectionsComplexIso,
    Functor.preimageIso_hom, Functor.map_preimage]
  change ((relativeGlobalSections X.hom).mapHomologicalComplex _).map
      ((CochainComplex.Plus.ι X.left.Modules).map
        ((pushforwardCompComplexIso h k).hom.app K)) ≫ _ = _
  simp only [pushforwardCompComplexIso, DerivedPlus.mapCochainComplexPlusCompIso,
    NatIso.ofComponents_hom_app, Functor.preimageIso_hom, Functor.map_preimage]
  ext i : 1
  exact pullbackComposition_sections h k (K.obj.X i)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
lemma pushforwardDerivedSectionsComparison_comp (h : Y ⟶ X) (k : Z ⟶ Y) :
    whiskerLeft (Scheme.Modules.pushforward k.left).mapCochainComplexPlus
        (pushforwardDerivedSectionsComparison h) ≫
      pushforwardDerivedSectionsComparison k =
    whiskerRight (pushforwardCompComplexIso h k).hom
        (DerivedCategory.Plus.Q ⋙ (relativeGlobalSections X.hom).rightDerivedFunctorPlus) ≫
      pushforwardDerivedSectionsComparison (k ≫ h) := by
  apply DerivedPlus.natTrans_ext_on_injective_complexes
  intro I
  let K := (InjectiveObject.ι Z.left.Modules).mapCochainComplexPlus.obj I
  let L := (Scheme.Modules.pushforward h.left).mapCochainComplexPlus.obj
    ((Scheme.Modules.pushforward k.left).mapCochainComplexPlus.obj K)
  let e := (pushforwardCompComplexIso h k).app K
  have he := (relativeGlobalSections X.hom).rightDerivedFunctorPlusUnit.naturality e.hom
  simp only [Functor.comp_map] at he
  have := isIso_unit_pushforward_injective_complex (k ≫ h) I
  have : IsIso ((relativeGlobalSections X.hom).rightDerivedFunctorPlusUnit.app L) := by
    rw [← isIso_comp_right_iff _
      ((relativeGlobalSections X.hom).rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Q.map e.hom))]
    erw [← he]
    infer_instance
  apply (cancel_epi
    ((relativeGlobalSections X.hom).rightDerivedFunctorPlusUnit.app L)).1
  change (relativeGlobalSections X.hom).rightDerivedFunctorPlusUnit.app L ≫
      ((pushforwardDerivedSectionsComparison h).app
          ((Scheme.Modules.pushforward k.left).mapCochainComplexPlus.obj K) ≫
        (pushforwardDerivedSectionsComparison k).app K) =
    (relativeGlobalSections X.hom).rightDerivedFunctorPlusUnit.app L ≫
      ((relativeGlobalSections X.hom).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map e.hom) ≫
        (pushforwardDerivedSectionsComparison (k ≫ h)).app K)
  rw [← reassoc_of% he]
  dsimp only [L]
  rw [← Category.assoc]
  rw [pushforwardDerivedSectionsComparison_fac h
      ((Scheme.Modules.pushforward k.left).mapCochainComplexPlus.obj K)]
  rw [Category.assoc]
  rw [pushforwardDerivedSectionsComparison_fac k K,
    pushforwardDerivedSectionsComparison_fac (k ≫ h) K]
  dsimp only [e]
  rw [← Functor.map_comp_assoc, ← pullbackComposition_sectionsComplex,
    Functor.map_comp, Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma relativeDerivedSectionsPullback_eq_comparison (h : Y ⟶ X) (M : X.left.Modules) :
    relativeDerivedSectionsPullback h M =
    (relativeGlobalSections X.hom).rightDerivedFunctorPlus.map
        (pullbackDerivedAugmentation h M) ≫
      (pushforwardDerivedSectionsComparison h).app
        (DerivedPlus.resolutionPlus
          (injectiveResolution ((Scheme.Modules.pullback h.left).obj M))) ≫
      (relativeGlobalSections Y.hom).rightDerivedFunctorPlus.map
        (DerivedPlus.singleIsoOfResolution
          (injectiveResolution ((Scheme.Modules.pullback h.left).obj M))).inv := by
  have := isIso_unit_pushforward_resolution h M
  let K := DerivedPlus.resolutionPlus
    (injectiveResolution ((Scheme.Modules.pullback h.left).obj M))
  have hb :
      inv ((relativeGlobalSections X.hom).rightDerivedFunctorPlusUnit.app
        ((Scheme.Modules.pushforward h.left).mapCochainComplexPlus.obj K)) ≫
      (DerivedCategory.Plus.Q.map (pullbackSectionsComplexIso h K).hom ≫
        (relativeGlobalSections Y.hom).rightDerivedFunctorPlusUnit.app K) =
      (pushforwardDerivedSectionsComparison h).app K := by
    rw [← pushforwardDerivedSectionsComparison_fac, IsIso.inv_hom_id_assoc]
  simp only [relativeDerivedSectionsPullback, DerivedPlus.derivedComplexIso,
    Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv, asIso_hom]
  rw [reassoc_of% hb]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma pullbackResolutionAugmentation_eq_single (h : Y ⟶ X) (M : X.left.Modules) :
    pullbackResolutionAugmentation h M =
      (CochainComplex.singleFunctor X.left.Modules 0).map
          ((Scheme.Modules.pullbackPushforwardAdjunction h.left).unit.app M) ≫
        (HomologicalComplex.singleMapHomologicalComplex
          (Scheme.Modules.pushforward h.left) (.up ℤ) 0).inv.app
          ((Scheme.Modules.pullback h.left).obj M) ≫
        ((Scheme.Modules.pushforward h.left).mapHomologicalComplex _).map
          (injectiveResolution ((Scheme.Modules.pullback h.left).obj M)).ι' := by
  apply HomologicalComplex.from_single_hom_ext
  simp only [pullbackResolutionAugmentation, HomologicalComplex.comp_f,
    HomologicalComplex.extendSingleIso_inv_f,
    HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := 0)
      (i' := (0 : ℤ)) (by simp),
    AcyclicResolution.mapAugmentation_f_zero, CochainComplex.singleFunctor,
    HomologicalComplex.single_map_f_self,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    Functor.mapHomologicalComplex_map_f, InjectiveResolution.ι'_f_zero]
  dsimp only [CochainComplex.single₀, Functor.id_obj]
  simp only [Category.assoc, DerivedPlus.extendXIso_inv_comp_mapExtendIso_hom,
    Iso.inv_hom_id_assoc, ← Functor.map_comp, CochainComplex.single₀ObjXSelf]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma pullbackDerivedAugmentation_eq_single (h : Y ⟶ X) (M : X.left.Modules) :
    pullbackDerivedAugmentation h M =
      (DerivedCategory.Plus.singleFunctor X.left.Modules 0).map
          ((Scheme.Modules.pullbackPushforwardAdjunction h.left).unit.app M) ≫
        (DerivedPlus.singlePlusQIso X.left.Modules).hom.app
          ((Scheme.Modules.pushforward h.left).obj
            ((Scheme.Modules.pullback h.left).obj M)) ≫
        DerivedCategory.Plus.Q.map
          ((DerivedPlus.singlePlusMapIso (Scheme.Modules.pushforward h.left)).hom.app
            ((Scheme.Modules.pullback h.left).obj M)) ≫
        DerivedCategory.Plus.Q.map
          ((Scheme.Modules.pushforward h.left).mapCochainComplexPlus.map
            (DerivedPlus.resolutionPlusι
              (injectiveResolution ((Scheme.Modules.pullback h.left).obj M)))) := by
  rw [← Functor.map_comp]
  have hs := (DerivedPlus.singlePlusQIso X.left.Modules).hom.naturality
    ((Scheme.Modules.pullbackPushforwardAdjunction h.left).unit.app M)
  simp only [Functor.comp_map] at hs
  rw [reassoc_of% hs]
  rw [← Functor.map_comp]
  apply DerivedCategory.Plus.ι.map_injective
  have h := (DerivedCategory.Plus.QCompιIso X.left.Modules).inv.naturality
    ((DerivedPlus.singlePlusFunctor X.left.Modules).map
        ((Scheme.Modules.pullbackPushforwardAdjunction h.left).unit.app M) ≫
      (DerivedPlus.singlePlusMapIso (Scheme.Modules.pushforward h.left)).hom.app
        ((Scheme.Modules.pullback h.left).obj M) ≫
      (Scheme.Modules.pushforward h.left).mapCochainComplexPlus.map
        (DerivedPlus.resolutionPlusι
          (injectiveResolution ((Scheme.Modules.pullback h.left).obj M))))
  simp only [Functor.comp_map] at h
  simp only [pullbackDerivedAugmentation, DerivedPlus.singlePlusQIso,
    NatIso.ofComponents_hom_app, Functor.map_comp, Functor.preimageIso_hom,
    Functor.map_preimage, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Category.assoc]
  simp only [Functor.map_comp, Category.assoc] at h
  refine congrArg (fun f =>
    (DerivedCategory.Plus.singleFunctorιIso X.left.Modules 0).hom.app M ≫
      (DerivedCategory.singleFunctorIsoCompQ X.left.Modules 0).hom.app M ≫ f) ?_
  refine Eq.trans ?_ h
  rw [pullbackResolutionAugmentation_eq_single]
  simp only [Functor.map_comp, Category.assoc, DerivedPlus.singlePlusMapIso,
    NatIso.ofComponents_hom_app, Functor.preimageIso_hom, Functor.map_preimage,
    Iso.symm_hom]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Pullback expressed on degree-zero complexes, without a chosen resolution. -/
lemma relativeDerivedSectionsPullback_eq_single (h : Y ⟶ X) (M : X.left.Modules) :
    relativeDerivedSectionsPullback h M =
      (relativeGlobalSections X.hom).rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.singleFunctor X.left.Modules 0).map
          ((Scheme.Modules.pullbackPushforwardAdjunction h.left).unit.app M) ≫
        (DerivedPlus.singlePlusQIso X.left.Modules).hom.app
          ((Scheme.Modules.pushforward h.left).obj
            ((Scheme.Modules.pullback h.left).obj M)) ≫
        DerivedCategory.Plus.Q.map
          ((DerivedPlus.singlePlusMapIso (Scheme.Modules.pushforward h.left)).hom.app
            ((Scheme.Modules.pullback h.left).obj M))) ≫
      (pushforwardDerivedSectionsComparison h).app
        ((DerivedPlus.singlePlusFunctor Y.left.Modules).obj
          ((Scheme.Modules.pullback h.left).obj M)) ≫
      (relativeGlobalSections Y.hom).rightDerivedFunctorPlus.map
        ((DerivedPlus.singlePlusQIso Y.left.Modules).inv.app
          ((Scheme.Modules.pullback h.left).obj M)) := by
  let N := (Scheme.Modules.pullback h.left).obj M
  let I := injectiveResolution N
  let a := DerivedPlus.resolutionPlusι I
  have hβ := (pushforwardDerivedSectionsComparison h).naturality a
  simp only [Functor.comp_map] at hβ
  have hs : DerivedCategory.Plus.Q.map a ≫ (DerivedPlus.singleIsoOfResolution I).inv =
      (DerivedPlus.singlePlusQIso Y.left.Modules).inv.app N := by
    apply (cancel_mono (DerivedPlus.singleIsoOfResolution I).hom).1
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      DerivedPlus.singleIsoOfResolution_hom_eq, Iso.inv_hom_id_app_assoc]
  rw [relativeDerivedSectionsPullback_eq_comparison,
    pullbackDerivedAugmentation_eq_single]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hβ, ← Functor.map_comp, hs]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
def pushforwardSingleDerivedSectionsComparison (h : Y ⟶ X) :
    Scheme.Modules.pushforward h.left ⋙
        DerivedPlus.derivedComplex (relativeGlobalSections X.hom) ⟶
      DerivedPlus.derivedComplex (relativeGlobalSections Y.hom) :=
  whiskerLeft (Scheme.Modules.pushforward h.left)
      (whiskerRight (DerivedPlus.singlePlusQIso X.left.Modules).hom
        (relativeGlobalSections X.hom).rightDerivedFunctorPlus) ≫
    whiskerRight (DerivedPlus.singlePlusMapIso (Scheme.Modules.pushforward h.left)).hom
      (DerivedCategory.Plus.Q ⋙ (relativeGlobalSections X.hom).rightDerivedFunctorPlus) ≫
    whiskerLeft (DerivedPlus.singlePlusFunctor Y.left.Modules)
      (pushforwardDerivedSectionsComparison h) ≫
    whiskerRight (DerivedPlus.singlePlusQIso Y.left.Modules).inv
      (relativeGlobalSections Y.hom).rightDerivedFunctorPlus

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
lemma pushforwardSingleDerivedSectionsComparison_comp (h : Y ⟶ X) (k : Z ⟶ Y)
    (N : Z.left.Modules) :
    (pushforwardSingleDerivedSectionsComparison h).app
        ((Scheme.Modules.pushforward k.left).obj N) ≫
      (pushforwardSingleDerivedSectionsComparison k).app N =
    (DerivedPlus.derivedComplex (relativeGlobalSections X.hom)).map
        ((Scheme.Modules.pushforwardComp k.left h.left).hom.app N) ≫
      (pushforwardSingleDerivedSectionsComparison (k ≫ h)).app N := by
  have hb := (pushforwardDerivedSectionsComparison h).naturality
    ((DerivedPlus.singlePlusMapIso (Scheme.Modules.pushforward k.left)).hom.app N)
  simp only [Functor.comp_map] at hb
  have hc := NatTrans.congr_app (pushforwardDerivedSectionsComparison_comp h k)
    ((DerivedPlus.singlePlusFunctor Z.left.Modules).obj N)
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    Functor.comp_map] at hc
  have hs := (DerivedPlus.singlePlusQIso X.left.Modules).hom.naturality
    ((Scheme.Modules.pushforwardComp k.left h.left).hom.app N)
  simp only [Functor.comp_map] at hs
  simp only [pushforwardSingleDerivedSectionsComparison, NatTrans.comp_app,
    whiskerLeft_app, whiskerRight_app, DerivedPlus.derivedComplex,
    Functor.comp_map, Category.assoc]
  rw [← Functor.map_comp_assoc _
    ((DerivedPlus.singlePlusQIso Y.left.Modules).inv.app _)
    ((DerivedPlus.singlePlusQIso Y.left.Modules).hom.app _),
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← reassoc_of% hb, reassoc_of% hc]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp]
  simp only [pushforwardCompComplexIso, Over.comp_left]
  rw [DerivedPlus.singlePlusMapIso_comp (Scheme.Modules.pushforwardComp k.left h.left) N]
  simp only [DerivedCategory.Plus.Q.map_comp]
  rw [← reassoc_of% hs]

set_option backward.isDefEq.respectTransparency false in
lemma relativeDerivedSectionsPullback_eq_unit_comparison (h : Y ⟶ X)
    (M : X.left.Modules) :
    relativeDerivedSectionsPullback h M =
      (DerivedPlus.derivedComplex (relativeGlobalSections X.hom)).map
        ((Scheme.Modules.pullbackPushforwardAdjunction h.left).unit.app M) ≫
      (pushforwardSingleDerivedSectionsComparison h).app
        ((Scheme.Modules.pullback h.left).obj M) := by
  rw [relativeDerivedSectionsPullback_eq_single]
  simp only [pushforwardSingleDerivedSectionsComparison, NatTrans.comp_app,
    whiskerLeft_app, whiskerRight_app, DerivedPlus.derivedComplex, Functor.comp_map,
    Functor.map_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
lemma pullbackComposition_unit (h : Y ⟶ X) (k : Z ⟶ Y) (M : X.left.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction h.left).unit.app M ≫
        (Scheme.Modules.pushforward h.left).map
          ((Scheme.Modules.pullbackPushforwardAdjunction k.left).unit.app
            ((Scheme.Modules.pullback h.left).obj M)) ≫
        (Scheme.Modules.pushforwardComp k.left h.left).hom.app
          ((Scheme.Modules.pullback k.left).obj ((Scheme.Modules.pullback h.left).obj M)) =
      (Scheme.Modules.pullbackPushforwardAdjunction (k ≫ h).left).unit.app M ≫
        (Scheme.Modules.pushforward (k ≫ h).left).map
          ((Scheme.Modules.pullbackComp k.left h.left).inv.app M) := by
  have H := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction h.left).comp
      (Scheme.Modules.pullbackPushforwardAdjunction k.left))
    (Scheme.Modules.pullbackPushforwardAdjunction (k ≫ h).left)
    (Scheme.Modules.pullbackComp k.left h.left).inv M
  erw [Scheme.Modules.conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at H
  simpa only [Category.assoc, Over.comp_left, Functor.comp_obj] using H

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma relativeDerivedSectionsPullback_comp_inv (h : Y ⟶ X) (k : Z ⟶ Y)
    (M : X.left.Modules) :
    relativeDerivedSectionsPullback h M ≫
        relativeDerivedSectionsPullback k ((Scheme.Modules.pullback h.left).obj M) =
      relativeDerivedSectionsPullback (k ≫ h) M ≫
        (DerivedPlus.derivedComplex (relativeGlobalSections Z.hom)).map
          ((Scheme.Modules.pullbackComp k.left h.left).inv.app M) := by
  have hn := (pushforwardSingleDerivedSectionsComparison h).naturality
    ((Scheme.Modules.pullbackPushforwardAdjunction k.left).unit.app
      ((Scheme.Modules.pullback h.left).obj M))
  simp only [Functor.comp_map] at hn
  have ht := (pushforwardSingleDerivedSectionsComparison (k ≫ h)).naturality
    ((Scheme.Modules.pullbackComp k.left h.left).inv.app M)
  simp only [Functor.comp_map] at ht
  rw [relativeDerivedSectionsPullback_eq_unit_comparison h,
    relativeDerivedSectionsPullback_eq_unit_comparison k,
    relativeDerivedSectionsPullback_eq_unit_comparison (k ≫ h)]
  simp only [Category.assoc]
  rw [← reassoc_of% hn, pushforwardSingleDerivedSectionsComparison_comp h k]
  simp only [← Functor.map_comp_assoc]
  rw [pullbackComposition_unit]
  simp only [Functor.map_comp, Category.assoc]
  simpa only [Functor.comp_obj, Over.comp_left] using congrArg
    (fun f => (DerivedPlus.derivedComplex (relativeGlobalSections X.hom)).map
      ((Scheme.Modules.pullbackPushforwardAdjunction (k ≫ h).left).unit.app M) ≫ f) ht

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
lemma relativeDerivedSectionsPullback_comp (h : Y ⟶ X) (k : Z ⟶ Y)
    (M : X.left.Modules) :
    relativeDerivedSectionsPullback h M ≫
        relativeDerivedSectionsPullback k ((Scheme.Modules.pullback h.left).obj M) ≫
        (DerivedPlus.derivedComplex (relativeGlobalSections Z.hom)).map
          ((Scheme.Modules.pullbackComp k.left h.left).hom.app M) =
      relativeDerivedSectionsPullback (k ≫ h) M := by
  rw [← Category.assoc, relativeDerivedSectionsPullback_comp_inv, Category.assoc,
    ← Functor.map_comp, Iso.inv_hom_id_app]
  dsimp only [Functor.id_obj, Over.comp_left]
  rw [(DerivedPlus.derivedComplex (relativeGlobalSections Z.hom)).map_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
lemma relativeCohomologyPullback_comp (h : Y ⟶ X) (k : Z ⟶ Y)
    (M : X.left.Modules) (n : ℕ) :
    relativeCohomologyPullback h M n ≫
        relativeCohomologyPullback k ((Scheme.Modules.pullback h.left).obj M) n ≫
        (relativeCohomology Z.hom n).map
          ((Scheme.Modules.pullbackComp k.left h.left).hom.app M) =
      relativeCohomologyPullback (k ≫ h) M n := by
  have hZ := DerivedPlus.homologyIso_hom_naturality (relativeGlobalSections Z.hom)
    ((Scheme.Modules.pullbackComp k.left h.left).hom.app M)
    (injectiveResolution
      ((Scheme.Modules.pullback k.left).obj ((Scheme.Modules.pullback h.left).obj M)))
    (injectiveResolution ((Scheme.Modules.pullback (k ≫ h).left).obj M)) n
  simp only [relativeCohomologyPullback, relativeCohomology, Category.assoc,
    Iso.hom_inv_id_assoc]
  rw [← hZ]
  simp only [← Functor.map_comp_assoc]
  rw [relativeDerivedSectionsPullback_comp]

/-- Composition law for the published actual relative-cohomology pullback. -/
theorem relativeCohomologyPullbackCompositionStatement :
    RelativeCohomologyPullbackCompositionStatement.{u} := by
  intro R X Y Z h k M n
  exact relativeCohomologyPullback_comp h k M n

end Langlands.AlgebraicGeometry.Modules.DerivedSections
