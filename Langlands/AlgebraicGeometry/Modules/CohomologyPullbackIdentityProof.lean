import Langlands.AlgebraicGeometry.Modules.CohomologyPullbackLawsStatement
import Langlands.Cohomology.DerivedPlusNaturality

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Cohomology

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

attribute [local instance] HasDerivedCategory.standard

variable {R : CommRingCat.{u}} {X Y : Over (Spec R)}

lemma pullbackIdentity_unit (M : X.left.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X.left)).unit.app M ≫
        (Scheme.Modules.pushforwardId X.left).hom.app
          ((Scheme.Modules.pullback (𝟙 X.left)).obj M) =
      (Scheme.Modules.pullbackId X.left).inv.app M := by
  apply (cancel_mono ((Scheme.Modules.pullbackId X.left).hom.app M)).mp
  have h := unit_conjugateEquiv Adjunction.id
    (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X.left))
    (Scheme.Modules.pullbackId X.left).hom M
  rw [Scheme.Modules.conjugateEquiv_pullbackId_hom] at h
  simp only [Adjunction.id_unit, NatTrans.id_app, Category.id_comp] at h
  have ht := (Scheme.Modules.pushforwardId X.left).hom.naturality
    ((Scheme.Modules.pullbackId X.left).hom.app M)
  simp only [Functor.id_map] at ht
  rw [Category.assoc, ← ht]
  rw [← Category.assoc, ← h]
  simp

def pushforwardIdentityCochainIso {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex X.left.Modules c) :
    ((Scheme.Modules.pushforward (𝟙 X.left)).mapHomologicalComplex c).obj K ≅ K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (Scheme.Modules.pushforwardId X.left).app (K.X i))
    (fun i j _ => ((Scheme.Modules.pushforwardId X.left).hom.naturality
      (K.d i j)).symm)

def pushforwardIdentityComplexIso (K : CochainComplex.Plus X.left.Modules) :
    (Scheme.Modules.pushforward (𝟙 X.left)).mapCochainComplexPlus.obj K ≅ K :=
  ObjectProperty.isoMk _ (pushforwardIdentityCochainIso K.obj)

lemma pushforwardIdentity_mapExtend {ι ι' : Type*} {c : ComplexShape ι}
    {c' : ComplexShape ι'} (K : HomologicalComplex X.left.Modules c)
    (e : c.Embedding c') :
    (DerivedPlus.mapExtendIso (Scheme.Modules.pushforward (𝟙 X.left)) K e).hom ≫
        (pushforwardIdentityCochainIso (K.extend e)).hom =
      HomologicalComplex.extendMap (pushforwardIdentityCochainIso K).hom e := by
  ext i : 1
  change (DerivedPlus.extendXMapIso (Scheme.Modules.pushforward (𝟙 X.left)) K
      (e.r i)).hom ≫
      (Scheme.Modules.pushforwardId X.left).hom.app
        (HomologicalComplex.extend.X K (e.r i)) =
    HomologicalComplex.extend.mapX (pushforwardIdentityCochainIso K).hom (e.r i)
  generalize e.r i = j
  cases j with
  | none => exact (HomologicalComplex.extend.isZero_X _ rfl).eq_of_src _ _
  | some j => exact Category.id_comp _

set_option backward.isDefEq.respectTransparency false in
lemma pullbackIdentity_natAugmentation (M : X.left.Modules) :
    ((CochainComplex.single₀ X.left.Modules).map
        ((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X.left)).unit.app M) ≫
      AcyclicResolution.mapAugmentation (Scheme.Modules.pushforward (𝟙 X.left))
        (injectiveResolution ((Scheme.Modules.pullback (𝟙 X.left)).obj M))) ≫
        (pushforwardIdentityCochainIso
          (injectiveResolution ((Scheme.Modules.pullback (𝟙 X.left)).obj M)).cocomplex).hom =
      (CochainComplex.single₀ X.left.Modules).map
          ((Scheme.Modules.pullbackId X.left).inv.app M) ≫
        (injectiveResolution ((Scheme.Modules.pullback (𝟙 X.left)).obj M)).ι := by
  apply HomologicalComplex.from_single_hom_ext
  simp only [HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero,
    AcyclicResolution.mapAugmentation_f_zero]
  change (_ ≫ (Scheme.Modules.pushforward (𝟙 X.left)).map
      (𝟙 _ ≫ (injectiveResolution ((Scheme.Modules.pullback (𝟙 X.left)).obj M)).ι.f 0)) ≫
      (Scheme.Modules.pushforwardId X.left).hom.app _ = _
  simp only [Category.id_comp, Category.assoc]
  have ht := (Scheme.Modules.pushforwardId X.left).hom.naturality
    ((injectiveResolution ((Scheme.Modules.pullback (𝟙 X.left)).obj M)).ι.f 0)
  simp only [Functor.id_map] at ht
  rw [ht, ← Category.assoc]
  erw [pullbackIdentity_unit (X := X) M]

set_option backward.isDefEq.respectTransparency false in
lemma pullbackIdentity_resolutionAugmentation (M : X.left.Modules) :
    pullbackResolutionAugmentation (𝟙 X) M ≫
        (pushforwardIdentityComplexIso
          (DerivedPlus.resolutionPlus
            (injectiveResolution ((Scheme.Modules.pullback (𝟙 X.left)).obj M)))).hom.hom =
      (CochainComplex.singleFunctor X.left.Modules 0).map
          ((Scheme.Modules.pullbackId X.left).inv.app M) ≫
        (injectiveResolution ((Scheme.Modules.pullback (𝟙 X.left)).obj M)).ι' := by
  have hs : (CochainComplex.singleFunctor X.left.Modules 0).map
        ((Scheme.Modules.pullbackId X.left).inv.app M) ≫
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
        ((Scheme.Modules.pullback (𝟙 X.left)).obj M) 0 0 rfl).inv =
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat M 0 0 rfl).inv ≫
      HomologicalComplex.extendMap ((CochainComplex.single₀ X.left.Modules).map
        ((Scheme.Modules.pullbackId X.left).inv.app M)) ComplexShape.embeddingUpNat := by
    apply HomologicalComplex.from_single_hom_ext
    simp only [HomologicalComplex.comp_f, HomologicalComplex.extendSingleIso_inv_f,
      HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := 0)
        (i' := (0 : ℤ)) (by simp), CochainComplex.singleFunctor,
      HomologicalComplex.single_map_f_self]
    cat_disch
  dsimp only [pullbackResolutionAugmentation, pushforwardIdentityComplexIso,
    ObjectProperty.isoMk, ObjectProperty.homMk, DerivedPlus.resolutionPlus,
    InjectiveResolution.cochainComplex, Over.id_left]
  simp only [Category.assoc]
  rw [pushforwardIdentity_mapExtend (X := X)
    (injectiveResolution ((Scheme.Modules.pullback (𝟙 X.left)).obj M)).cocomplex
    ComplexShape.embeddingUpNat]
  rw [← HomologicalComplex.extendMap_comp,
    pullbackIdentity_natAugmentation (X := X),
    HomologicalComplex.extendMap_comp]
  simp only [InjectiveResolution.ι', ComplexShape.Embedding.extendFunctor_map,
    ← Category.assoc]
  rw [hs]

set_option backward.isDefEq.respectTransparency false in
lemma pullbackIdentity_derivedAugmentation (M : X.left.Modules) :
    pullbackDerivedAugmentation (𝟙 X) M ≫
        DerivedCategory.Plus.Q.map
          (pushforwardIdentityComplexIso
            (DerivedPlus.resolutionPlus
              (injectiveResolution ((Scheme.Modules.pullback (𝟙 X.left)).obj M)))).hom =
      (DerivedCategory.Plus.singleFunctor X.left.Modules 0).map
          ((Scheme.Modules.pullbackId X.left).inv.app M) ≫
        (DerivedPlus.singleIsoOfResolution
          (injectiveResolution ((Scheme.Modules.pullback (𝟙 X.left)).obj M))).hom := by
  apply DerivedCategory.Plus.ι.map_injective
  have h₁ := (DerivedCategory.Plus.singleFunctorιIso X.left.Modules 0).hom.naturality
    ((Scheme.Modules.pullbackId X.left).inv.app M)
  have h₂ := (DerivedCategory.singleFunctorIsoCompQ X.left.Modules 0).hom.naturality
    ((Scheme.Modules.pullbackId X.left).inv.app M)
  have h₃ := (DerivedCategory.Plus.QCompιIso X.left.Modules).inv.naturality
    (pushforwardIdentityComplexIso
      (DerivedPlus.resolutionPlus
        (injectiveResolution ((Scheme.Modules.pullback (𝟙 X.left)).obj M)))).hom
  have h₄ := congrArg DerivedCategory.Q.map
    (pullbackIdentity_resolutionAugmentation (X := X) M)
  simp only [Functor.comp_map] at h₁ h₂ h₃
  simp only [Functor.map_comp] at h₄
  simp only [Functor.map_comp, pullbackDerivedAugmentation, Functor.map_preimage,
    DerivedPlus.ι_map_singleIsoOfResolution_hom, Category.assoc]
  rw [reassoc_of% h₁, reassoc_of% h₂, ← reassoc_of% h₄]
  exact congrArg (fun g =>
    (DerivedCategory.Plus.singleFunctorιIso X.left.Modules 0).hom.app M ≫
      (DerivedCategory.singleFunctorIsoCompQ X.left.Modules 0).hom.app M ≫
        DerivedCategory.Q.map (pullbackResolutionAugmentation (𝟙 X) M) ≫ g) h₃.symm

set_option backward.isDefEq.respectTransparency false in
lemma pullbackIdentity_sections (M : X.left.Modules) :
    (relativePushforwardSectionsIso (𝟙 X)).hom.app M =
      (relativeGlobalSections X.hom).map
        ((Scheme.Modules.pushforwardId X.left).hom.app M) := by
  change moduleSpecΓFunctor.map ((Scheme.Modules.pushforwardComp (𝟙 X.left) X.hom).hom.app M) ≫
      moduleSpecΓFunctor.map ((Scheme.Modules.pushforwardCongr (Over.w (𝟙 X))).hom.app M) =
    moduleSpecΓFunctor.map
      ((Scheme.Modules.pushforward X.hom).map ((Scheme.Modules.pushforwardId X.left).hom.app M))
  rw [← Functor.map_comp]
  congr 1
  apply Scheme.Modules.hom_ext
  intro U
  simp
  exact M.presheaf.map_id _

set_option backward.isDefEq.respectTransparency false in
lemma pullbackIdentity_sectionsComplex (K : CochainComplex.Plus X.left.Modules) :
    (pullbackSectionsComplexIso (𝟙 X) K).hom =
      (relativeGlobalSections X.hom).mapCochainComplexPlus.map
        (pushforwardIdentityComplexIso K).hom := by
  apply (CochainComplex.Plus.ι _).map_injective
  simp only [pullbackSectionsComplexIso, Functor.preimageIso_hom, Functor.map_preimage]
  ext i : 1
  exact pullbackIdentity_sections (X := X) (K.obj.X i)

set_option backward.isDefEq.respectTransparency false in
lemma relativeDerivedSectionsPullback_identity (M : X.left.Modules) :
    relativeDerivedSectionsPullback (𝟙 X) M =
      (DerivedPlus.derivedComplex (relativeGlobalSections X.hom)).map
        ((Scheme.Modules.pullbackId X.left).inv.app M) := by
  let I := injectiveResolution ((Scheme.Modules.pullback (𝟙 X.left)).obj M)
  let K := DerivedPlus.resolutionPlus I
  let L := (Scheme.Modules.pushforward (𝟙 X.left)).mapCochainComplexPlus.obj K
  let t := pushforwardIdentityComplexIso K
  have hL (i : ℤ) (q : ℕ) :
      IsZero (((relativeGlobalSections X.hom).rightDerived (q + 1)).obj (L.obj.X i)) :=
    (pushforwardInjectiveAcyclic X.left X.left (𝟙 X.left) (K.obj.X i)
      inferInstance q).2 R X.hom
  have := acyclicTermsDerivedUnitStatement X.left.Modules (ModuleCat.{u} R)
    (relativeGlobalSections X.hom) L hL
  have hη := (relativeGlobalSections X.hom).rightDerivedFunctorPlusUnit.naturality t.hom
  simp only [Functor.comp_map] at hη
  have hη' :
      inv ((relativeGlobalSections X.hom).rightDerivedFunctorPlusUnit.app L) ≫
        DerivedCategory.Plus.Q.map
          ((relativeGlobalSections X.hom).mapCochainComplexPlus.map t.hom) =
      (relativeGlobalSections X.hom).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map t.hom) ≫
        inv ((relativeGlobalSections X.hom).rightDerivedFunctorPlusUnit.app K) := by
    symm
    rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
    exact hη.symm
  change (relativeGlobalSections X.hom).rightDerivedFunctorPlus.map
      (pullbackDerivedAugmentation (𝟙 X) M) ≫
    inv ((relativeGlobalSections X.hom).rightDerivedFunctorPlusUnit.app L) ≫
    DerivedCategory.Plus.Q.map (pullbackSectionsComplexIso (𝟙 X) K).hom ≫
    (DerivedPlus.derivedComplexIso (relativeGlobalSections X.hom) I).inv = _
  rw [pullbackIdentity_sectionsComplex (X := X), reassoc_of% hη',
    ← Functor.map_comp_assoc, pullbackIdentity_derivedAugmentation (X := X),
    Functor.map_comp, Category.assoc]
  rw [← Category.assoc
    ((relativeGlobalSections X.hom).rightDerivedFunctorPlus.map
      (DerivedPlus.singleIsoOfResolution I).hom)
    (inv ((relativeGlobalSections X.hom).rightDerivedFunctorPlusUnit.app K))
    (DerivedPlus.derivedComplexIso (relativeGlobalSections X.hom) I).inv]
  change (relativeGlobalSections X.hom).rightDerivedFunctorPlus.map
      ((DerivedCategory.Plus.singleFunctor X.left.Modules 0).map
        ((Scheme.Modules.pullbackId X.left).inv.app M)) ≫
      (DerivedPlus.derivedComplexIso (relativeGlobalSections X.hom) I).hom ≫
        (DerivedPlus.derivedComplexIso (relativeGlobalSections X.hom) I).inv = _
  simp
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma relativeCohomologyPullback_identity (M : X.left.Modules) (n : ℕ) :
    relativeCohomologyPullback (𝟙 X) M n ≫
        (relativeCohomology X.hom n).map
          ((Scheme.Modules.pullbackId X.left).hom.app M) =
      𝟙 _ := by
  have h := DerivedPlus.homologyIso_hom_naturality (relativeGlobalSections X.hom)
    ((Scheme.Modules.pullbackId X.left).inv.app M) (injectiveResolution M)
    (injectiveResolution ((Scheme.Modules.pullback (𝟙 X.left)).obj M)) n
  simp only [relativeCohomologyPullback, relativeCohomology,
    relativeDerivedSectionsPullback_identity,
    Category.assoc]
  rw [reassoc_of% h]
  simp only [← Functor.map_comp, Iso.inv_hom_id_app]
  dsimp only [Functor.id_obj]
  rw [CategoryTheory.Functor.map_id]
  simp

/-- The identity law for the published actual relative-cohomology pullback. -/
theorem relativeCohomologyPullbackIdentityStatement :
    RelativeCohomologyPullbackIdentityStatement.{u} := by
  intro R X M n
  exact relativeCohomologyPullback_identity M n

end Langlands.AlgebraicGeometry.Modules.DerivedSections
