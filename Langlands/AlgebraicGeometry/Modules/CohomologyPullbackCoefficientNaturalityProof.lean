import Langlands.AlgebraicGeometry.Modules.CohomologyPullbackLawsStatement
import Langlands.Cohomology.DerivedPlusNaturality

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Cohomology

namespace Langlands.Cohomology.AcyclicResolution

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  (F : C ⥤ D) [F.Additive] {A B : C} {f : A ⟶ B}
  {I : InjectiveResolution A} {J : InjectiveResolution B}

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
lemma mapAugmentation_naturality_hom (φ : I.Hom J f) :
    (CochainComplex.single₀ D).map (F.map f) ≫ mapAugmentation F J =
      mapAugmentation F I ≫ (F.mapHomologicalComplex _).map φ.hom := by
  apply HomologicalComplex.from_single_hom_ext
  have H : f ≫ J.ι.f 0 = I.ι.f 0 ≫ φ.hom.f 0 := by
    simpa only [CochainComplex.single₀_map_f_zero] using φ.ι_f_zero_comp_hom_f_zero.symm
  simp only [HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero,
    mapAugmentation_f_zero, Functor.mapHomologicalComplex_map_f,
    CochainComplex.single₀ObjXSelf, Iso.refl_inv]
  change F.map f ≫ F.map (𝟙 B ≫ J.ι.f 0) =
    F.map (𝟙 A ≫ I.ι.f 0) ≫ F.map (φ.hom.f 0)
  simp only [Category.id_comp]
  rw [← F.map_comp, ← F.map_comp]
  exact congrArg F.map H

end Langlands.Cohomology.AcyclicResolution

namespace Langlands.Cohomology.DerivedPlus

variable {C : Type*} [Category* C] [Abelian C]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma extendSingleIso_inv_naturality {A B : C} (f : A ⟶ B) :
    (CochainComplex.singleFunctor C 0).map f ≫
        (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat B 0 0 rfl).inv =
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat A 0 0 rfl).inv ≫
        HomologicalComplex.extendMap ((CochainComplex.single₀ C).map f)
          ComplexShape.embeddingUpNat := by
  apply HomologicalComplex.from_single_hom_ext
  simp only [HomologicalComplex.comp_f, HomologicalComplex.extendSingleIso_inv_f,
    HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := 0)
      (i' := (0 : ℤ)) (by simp), CochainComplex.singleFunctor,
    HomologicalComplex.single_map_f_self]
  cat_disch

end Langlands.Cohomology.DerivedPlus

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

attribute [local instance] HasDerivedCategory.standard

variable {R : CommRingCat.{u}} {X Y : Over (Spec R)}

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma pullbackResolutionAugmentation_naturality (h : Y ⟶ X)
    {M M' : X.left.Modules} (f : M ⟶ M')
    (φ : (injectiveResolution ((Scheme.Modules.pullback h.left).obj M)).Hom
      (injectiveResolution ((Scheme.Modules.pullback h.left).obj M'))
        ((Scheme.Modules.pullback h.left).map f)) :
    (CochainComplex.singleFunctor X.left.Modules 0).map f ≫
        pullbackResolutionAugmentation h M' =
      pullbackResolutionAugmentation h M ≫
        ((Scheme.Modules.pushforward h.left).mapHomologicalComplex _).map φ.hom' := by
  have H : (CochainComplex.single₀ X.left.Modules).map f ≫
      ((CochainComplex.single₀ X.left.Modules).map
        ((Scheme.Modules.pullbackPushforwardAdjunction h.left).unit.app M') ≫
          AcyclicResolution.mapAugmentation (Scheme.Modules.pushforward h.left)
            (injectiveResolution ((Scheme.Modules.pullback h.left).obj M'))) =
      ((CochainComplex.single₀ X.left.Modules).map
        ((Scheme.Modules.pullbackPushforwardAdjunction h.left).unit.app M) ≫
          AcyclicResolution.mapAugmentation (Scheme.Modules.pushforward h.left)
            (injectiveResolution ((Scheme.Modules.pullback h.left).obj M))) ≫
        ((Scheme.Modules.pushforward h.left).mapHomologicalComplex _).map φ.hom := by
    have Hη := (Scheme.Modules.pullbackPushforwardAdjunction h.left).unit.naturality f
    dsimp at Hη
    rw [← Functor.map_comp_assoc, Hη]
    simp only [Functor.map_comp, Category.assoc]
    rw [AcyclicResolution.mapAugmentation_naturality_hom]
  simp only [pullbackResolutionAugmentation, Category.assoc]
  rw [DerivedPlus.extendSingleIso_inv_naturality_assoc]
  rw [InjectiveResolution.Hom.hom', DerivedPlus.mapExtendIso_hom_naturality]
  simp only [← Category.assoc, ← HomologicalComplex.extendMap_comp]
  simp only [Category.assoc] at H ⊢
  rw [H]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma pullbackDerivedAugmentation_naturality (h : Y ⟶ X)
    {M M' : X.left.Modules} (f : M ⟶ M')
    (φ : (injectiveResolution ((Scheme.Modules.pullback h.left).obj M)).Hom
      (injectiveResolution ((Scheme.Modules.pullback h.left).obj M'))
        ((Scheme.Modules.pullback h.left).map f)) :
    (DerivedCategory.Plus.singleFunctor X.left.Modules 0).map f ≫
        pullbackDerivedAugmentation h M' =
      pullbackDerivedAugmentation h M ≫ DerivedCategory.Plus.Q.map
        ((Scheme.Modules.pushforward h.left).mapCochainComplexPlus.map
          (DerivedPlus.resolutionPlusMap φ)) := by
  apply DerivedCategory.Plus.ι.map_injective
  have h₁ := (DerivedCategory.Plus.singleFunctorιIso X.left.Modules 0).hom.naturality f
  have h₂ := (DerivedCategory.singleFunctorIsoCompQ X.left.Modules 0).hom.naturality f
  have h₃ := (DerivedCategory.Plus.QCompιIso X.left.Modules).inv.naturality
    ((Scheme.Modules.pushforward h.left).mapCochainComplexPlus.map
      (DerivedPlus.resolutionPlusMap φ))
  have h₄ := congrArg DerivedCategory.Q.map
    (pullbackResolutionAugmentation_naturality h f φ)
  simp only [Functor.comp_map] at h₁ h₂ h₃
  simp only [Functor.map_comp] at h₄
  simp only [Functor.map_comp, pullbackDerivedAugmentation, Functor.map_preimage,
    Category.assoc]
  rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₄, ← h₃]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma pullbackSectionsComplexIso_hom_naturality (h : Y ⟶ X)
    {K L : CochainComplex.Plus Y.left.Modules} (ψ : K ⟶ L) :
    (relativeGlobalSections X.hom).mapCochainComplexPlus.map
        ((Scheme.Modules.pushforward h.left).mapCochainComplexPlus.map ψ) ≫
        (pullbackSectionsComplexIso h L).hom =
      (pullbackSectionsComplexIso h K).hom ≫
        (relativeGlobalSections Y.hom).mapCochainComplexPlus.map ψ := by
  apply (CochainComplex.Plus.ι _).map_injective
  simp only [Functor.map_comp, pullbackSectionsComplexIso,
    Functor.preimageIso_hom, Functor.map_preimage]
  exact (Functor.mapHomologicalComplexCompIso (relativePushforwardSectionsIso h) _).hom.naturality
    ψ.hom

lemma isIso_unit_pushforward_resolution (h : Y ⟶ X) (M : X.left.Modules) :
    IsIso ((relativeGlobalSections X.hom).rightDerivedFunctorPlusUnit.app
      ((Scheme.Modules.pushforward h.left).mapCochainComplexPlus.obj
        (DerivedPlus.resolutionPlus
          (injectiveResolution ((Scheme.Modules.pullback h.left).obj M))))) := by
  apply acyclicTermsDerivedUnitStatement
  intro i q
  let I := injectiveResolution ((Scheme.Modules.pullback h.left).obj M)
  exact (pushforwardInjectiveAcyclic Y.left X.left h.left (I.cochainComplex.X i)
    inferInstance q).2 R X.hom

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma relativeDerivedSectionsPullback_naturality (h : Y ⟶ X)
    {M M' : X.left.Modules} (f : M ⟶ M') :
    (DerivedPlus.derivedComplex (relativeGlobalSections X.hom)).map f ≫
        relativeDerivedSectionsPullback h M' =
      relativeDerivedSectionsPullback h M ≫
        (DerivedPlus.derivedComplex (relativeGlobalSections Y.hom)).map
          ((Scheme.Modules.pullback h.left).map f) := by
  let I := injectiveResolution ((Scheme.Modules.pullback h.left).obj M)
  let J := injectiveResolution ((Scheme.Modules.pullback h.left).obj M')
  let φ := DerivedPlus.descHom ((Scheme.Modules.pullback h.left).map f) I J
  let ψ := DerivedPlus.resolutionPlusMap φ
  have := isIso_unit_pushforward_resolution h M
  have := isIso_unit_pushforward_resolution h M'
  have h₁ := pullbackDerivedAugmentation_naturality h f φ
  have h₂ := (relativeGlobalSections X.hom).rightDerivedFunctorPlusUnit.naturality
    ((Scheme.Modules.pushforward h.left).mapCochainComplexPlus.map ψ)
  have h₃ := pullbackSectionsComplexIso_hom_naturality h ψ
  have h₄ := DerivedPlus.derivedComplexIso_hom_naturality
    (relativeGlobalSections Y.hom) φ
  simp only [Functor.comp_map] at h₂
  have h₂' : (relativeGlobalSections X.hom).rightDerivedFunctorPlus.map
      (DerivedCategory.Plus.Q.map
        ((Scheme.Modules.pushforward h.left).mapCochainComplexPlus.map ψ)) ≫
      inv ((relativeGlobalSections X.hom).rightDerivedFunctorPlusUnit.app
        ((Scheme.Modules.pushforward h.left).mapCochainComplexPlus.obj
          (DerivedPlus.resolutionPlus J))) =
    inv ((relativeGlobalSections X.hom).rightDerivedFunctorPlusUnit.app
        ((Scheme.Modules.pushforward h.left).mapCochainComplexPlus.obj
          (DerivedPlus.resolutionPlus I))) ≫
      DerivedCategory.Plus.Q.map ((relativeGlobalSections X.hom).mapCochainComplexPlus.map
        ((Scheme.Modules.pushforward h.left).mapCochainComplexPlus.map ψ)) := by
    rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
    exact h₂.symm
  have h₃' := congrArg DerivedCategory.Plus.Q.map h₃
  simp only [Functor.map_comp] at h₃'
  have h₄' : DerivedCategory.Plus.Q.map
      ((relativeGlobalSections Y.hom).mapCochainComplexPlus.map ψ) ≫
      (DerivedPlus.derivedComplexIso (relativeGlobalSections Y.hom) J).inv =
    (DerivedPlus.derivedComplexIso (relativeGlobalSections Y.hom) I).inv ≫
      (DerivedPlus.derivedComplex (relativeGlobalSections Y.hom)).map
        ((Scheme.Modules.pullback h.left).map f) := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
    exact h₄.symm
  simp only [relativeDerivedSectionsPullback, Category.assoc]
  change (relativeGlobalSections X.hom).rightDerivedFunctorPlus.map
    ((DerivedCategory.Plus.singleFunctor X.left.Modules 0).map f) ≫ _ = _
  rw [← Functor.map_comp_assoc, h₁, Functor.map_comp, Category.assoc,
    reassoc_of% h₂', reassoc_of% h₃', h₄']

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma relativeCohomologyPullback_naturality (h : Y ⟶ X)
    {M M' : X.left.Modules} (f : M ⟶ M') (n : ℕ) :
    (relativeCohomology X.hom n).map f ≫ relativeCohomologyPullback h M' n =
      relativeCohomologyPullback h M n ≫
        (relativeCohomology Y.hom n).map ((Scheme.Modules.pullback h.left).map f) := by
  have hX := DerivedPlus.homologyIso_hom_naturality (relativeGlobalSections X.hom)
    f (injectiveResolution M) (injectiveResolution M') n
  have hY := DerivedPlus.homologyIso_hom_naturality (relativeGlobalSections Y.hom)
    ((Scheme.Modules.pullback h.left).map f)
    (injectiveResolution ((Scheme.Modules.pullback h.left).obj M))
    (injectiveResolution ((Scheme.Modules.pullback h.left).obj M')) n
  have hD := congrArg (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) n).map
    (relativeDerivedSectionsPullback_naturality h f)
  simp only [Functor.map_comp] at hD
  have hX' : (relativeCohomology X.hom n).map f ≫
      (DerivedPlus.homologyIso (relativeGlobalSections X.hom) (injectiveResolution M') n).inv =
    (DerivedPlus.homologyIso (relativeGlobalSections X.hom) (injectiveResolution M) n).inv ≫
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) n).map
        ((DerivedPlus.derivedComplex (relativeGlobalSections X.hom)).map f) := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
    exact hX.symm
  simp only [relativeCohomologyPullback, Category.assoc]
  rw [reassoc_of% hX', reassoc_of% hD, hY]
  rfl

/-- Canonical actual relative-cohomology pullback is natural in coefficients. -/
theorem relativeCohomologyPullbackCoefficientNaturalityStatement :
    RelativeCohomologyPullbackCoefficientNaturalityStatement.{u} := by
  intro R X Y h M M' f n
  exact relativeCohomologyPullback_naturality h f n

end Langlands.AlgebraicGeometry.Modules.DerivedSections
