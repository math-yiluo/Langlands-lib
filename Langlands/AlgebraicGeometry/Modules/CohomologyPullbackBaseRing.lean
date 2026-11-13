import Langlands.AlgebraicGeometry.Modules.CohomologyPullbackCompositionProof
import Langlands.AlgebraicGeometry.Modules.DerivedBaseChange

/-!
# Canonical cohomology pullback and change of the affine base ring
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry
open Langlands.Cohomology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Cohomology.DerivedPlus

section BaseChangeTransformation

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E] [EnoughInjectives C]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  (G : C ⥤ D) [G.Additive] (P : D ⥤ E) [P.Additive]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  {H : C ⥤ E} [H.Additive] (e : G ⋙ P ≅ H)

/-- The termwise comparison between `P` applied to the localized image of a
bounded below complex under `G` and its localized image under `H`. -/
def plusTermwiseIso :
    G.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.ι ⋙
        P.mapDerivedCategory ≅
      H.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.ι :=
  NatIso.ofComponents
    (fun K => P.mapDerivedCategory.mapIso
        ((DerivedCategory.Plus.QCompιIso D).app (G.mapCochainComplexPlus.obj K)) ≪≫
      P.mapDerivedCategoryFactors.app ((G.mapHomologicalComplex _).obj K.obj) ≪≫
      DerivedCategory.Q.mapIso ((Functor.mapHomologicalComplexCompIso e _).app K.obj) ≪≫
      ((DerivedCategory.Plus.QCompιIso E).app (H.mapCochainComplexPlus.obj K)).symm)
    (fun {K L} f => by
      have h₁ : DerivedCategory.Plus.ι.map
            (DerivedCategory.Plus.Q.map (G.mapCochainComplexPlus.map f)) ≫
            (DerivedCategory.Plus.QCompιIso D).hom.app (G.mapCochainComplexPlus.obj L) =
          (DerivedCategory.Plus.QCompιIso D).hom.app (G.mapCochainComplexPlus.obj K) ≫
            DerivedCategory.Q.map ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map f.hom) :=
        (DerivedCategory.Plus.QCompιIso D).hom.naturality (G.mapCochainComplexPlus.map f)
      have h₂ := P.mapDerivedCategoryFactors.hom.naturality
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map f.hom)
      have h₃ := (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom.naturality f.hom
      have h₄ : DerivedCategory.Q.map ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map f.hom) ≫
            (DerivedCategory.Plus.QCompιIso E).inv.app (H.mapCochainComplexPlus.obj L) =
          (DerivedCategory.Plus.QCompιIso E).inv.app (H.mapCochainComplexPlus.obj K) ≫
            DerivedCategory.Plus.ι.map
              (DerivedCategory.Plus.Q.map (H.mapCochainComplexPlus.map f)) :=
        (DerivedCategory.Plus.QCompιIso E).inv.naturality (H.mapCochainComplexPlus.map f)
      simp only [Functor.comp_map, Functor.comp_obj] at h₂ h₃
      simp only [Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
        Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv, Category.assoc]
      rw [← Functor.map_comp_assoc, h₁, Functor.map_comp_assoc, reassoc_of% h₂,
        ← Functor.map_comp_assoc, h₃, Functor.map_comp_assoc]
      exact congrArg (fun q => _ ≫ _ ≫ _ ≫ q) h₄)

/-- The composite of the right derived functor of `H` with the inclusion is a
right derived functor of `H` followed by localization and inclusion. -/
instance isRightDerivedFunctor_rightDerivedFunctorPlus_comp_ι :
    (H.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).IsRightDerivedFunctor
      (whiskerRight H.rightDerivedFunctorPlusUnit DerivedCategory.Plus.ι)
      (CochainComplex.Plus.quasiIso C) := by
  let Φ := CochainComplex.Plus.localizerMorphism C
  have hT : Φ.Derives
      (H.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.ι) :=
    MorphismProperty.IsInvertedBy.of_comp _
      (Φ.functor ⋙ H.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q)
      (CochainComplex.Plus.localizerMorphism_derives_mapCochainComplexPlus H)
      DerivedCategory.Plus.ι
  have hα (K : CochainComplex.Plus (InjectiveObject C)) :
      IsIso ((whiskerRight H.rightDerivedFunctorPlusUnit DerivedCategory.Plus.ι).app
        (Φ.functor.obj K)) := by
    dsimp [Φ]
    infer_instance
  exact hT.isRightDerivedFunctor_of_isIso _ hα

/-- The comparison `R H ⟶ P ∘ R G` of right derived functors, induced by the
termwise comparison and the universal property of `R H`. -/
def baseChangeTrans :
    H.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι ⟶
      G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι ⋙ P.mapDerivedCategory :=
  (H.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).rightDerivedDesc
    (whiskerRight H.rightDerivedFunctorPlusUnit DerivedCategory.Plus.ι)
    (CochainComplex.Plus.quasiIso C)
    (G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι ⋙ P.mapDerivedCategory)
    ((plusTermwiseIso G P e).inv ≫
      whiskerRight G.rightDerivedFunctorPlusUnit
        (DerivedCategory.Plus.ι ⋙ P.mapDerivedCategory))

@[reassoc]
lemma baseChangeTrans_fac (K : CochainComplex.Plus C) :
    DerivedCategory.Plus.ι.map (H.rightDerivedFunctorPlusUnit.app K) ≫
        (baseChangeTrans G P e).app (DerivedCategory.Plus.Q.obj K) =
      (plusTermwiseIso G P e).inv.app K ≫
        P.mapDerivedCategory.map
          (DerivedCategory.Plus.ι.map (G.rightDerivedFunctorPlusUnit.app K)) :=
  Functor.rightDerived_fac_app (H.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι)
    (whiskerRight H.rightDerivedFunctorPlusUnit DerivedCategory.Plus.ι)
    (CochainComplex.Plus.quasiIso C)
    (G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι ⋙ P.mapDerivedCategory)
    ((plusTermwiseIso G P e).inv ≫
      whiskerRight G.rightDerivedFunctorPlusUnit
        (DerivedCategory.Plus.ι ⋙ P.mapDerivedCategory)) K

/-- On a complex where both units are invertible, the comparison is the termwise one. -/
lemma baseChangeTrans_app_of_isIso (K : CochainComplex.Plus C)
    [IsIso (H.rightDerivedFunctorPlusUnit.app K)] :
    (baseChangeTrans G P e).app (DerivedCategory.Plus.Q.obj K) =
      inv (DerivedCategory.Plus.ι.map (H.rightDerivedFunctorPlusUnit.app K)) ≫
        (plusTermwiseIso G P e).inv.app K ≫
        P.mapDerivedCategory.map
          (DerivedCategory.Plus.ι.map (G.rightDerivedFunctorPlusUnit.app K)) := by
  rw [IsIso.eq_inv_comp, baseChangeTrans_fac]

/-- The comparison at a single object, transported to an injective resolution. -/
@[reassoc]
lemma derivedComplexIso_inv_baseChangeTrans {X : C} (I : InjectiveResolution X) :
    DerivedCategory.Plus.ι.map (derivedComplexIso H I).inv ≫
        (baseChangeTrans G P e).app ((DerivedCategory.Plus.singleFunctor C 0).obj X) =
      (plusTermwiseIso G P e).inv.app (resolutionPlus I) ≫
        P.mapDerivedCategory.map (DerivedCategory.Plus.ι.map (derivedComplexIso G I).inv) := by
  have hn := (baseChangeTrans G P e).naturality (singleIsoOfResolution I).inv
  simp only [Functor.comp_map] at hn
  simp only [derivedComplexIso, Iso.trans_inv, Iso.symm_inv, asIso_hom, Functor.mapIso_inv,
    Functor.map_comp, Category.assoc]
  rw [hn, baseChangeTrans_fac_assoc]

/-- At a single object, the comparison is the inverse of `derivedCompIso`. -/
lemma baseChangeTrans_single (X : C) :
    (baseChangeTrans G P e).app ((DerivedCategory.Plus.singleFunctor C 0).obj X) =
      (derivedCompIso G P e).inv.app X := by
  let I := injectiveResolution X
  have hθ : (baseChangeTrans G P e).app ((DerivedCategory.Plus.singleFunctor C 0).obj X) =
      DerivedCategory.Plus.ι.map (derivedComplexIso H I).hom ≫
        (plusTermwiseIso G P e).inv.app (resolutionPlus I) ≫
        P.mapDerivedCategory.map (DerivedCategory.Plus.ι.map (derivedComplexIso G I).inv) := by
    rw [← derivedComplexIso_inv_baseChangeTrans, ← Functor.map_comp_assoc, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  have hc : (derivedCompIso G P e).hom.app X =
      P.mapDerivedCategory.map (DerivedCategory.Plus.ι.map (derivedComplexIso G I).hom) ≫
        (plusTermwiseIso G P e).hom.app (resolutionPlus I) ≫
        DerivedCategory.Plus.ι.map (derivedComplexIso H I).inv := by
    rw [← cancel_mono (AcyclicResolution.derivedResolutionIso H I).hom,
      derivedCompIso_hom_resolution,
      resolutionPostcompNatIso_hom_app_comp_resolutionCongrNatIso_hom_app]
    simp only [AcyclicResolution.derivedResolutionIso, Iso.trans_hom, Functor.mapIso_hom,
      Iso.app_hom, Functor.map_comp, Category.assoc, plusTermwiseIso, NatIso.ofComponents_hom_app,
      Iso.symm_hom]
    rw [← Functor.map_comp_assoc DerivedCategory.Plus.ι (derivedComplexIso H I).inv,
      Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
    simp only [Iso.app_inv, Iso.inv_hom_id_app]
    erw [Category.comp_id]
    rfl
  rw [hθ]
  refine ((Iso.app (derivedCompIso G P e) X).hom_comp_eq_id).1 ?_
  simp only [Iso.app_hom, hc, Category.assoc]
  rw [← Functor.map_comp_assoc DerivedCategory.Plus.ι (derivedComplexIso H I).inv,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app_assoc,
    ← Functor.map_comp, ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id]
  rfl

/-- On a complex where both units are invertible, the inverse unit followed by
the inverse termwise comparison factors through the comparison. -/
@[reassoc]
lemma inv_unit_comp_plusTermwiseIso_inv (K : CochainComplex.Plus C)
    [IsIso (H.rightDerivedFunctorPlusUnit.app K)] [IsIso (G.rightDerivedFunctorPlusUnit.app K)] :
    DerivedCategory.Plus.ι.map (inv (H.rightDerivedFunctorPlusUnit.app K)) ≫
        (plusTermwiseIso G P e).inv.app K =
      (baseChangeTrans G P e).app (DerivedCategory.Plus.Q.obj K) ≫
        P.mapDerivedCategory.map
          (DerivedCategory.Plus.ι.map (inv (G.rightDerivedFunctorPlusUnit.app K))) := by
  rw [baseChangeTrans_app_of_isIso]
  simp only [Functor.map_inv, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

end BaseChangeTransformation

end Langlands.Cohomology.DerivedPlus

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

attribute [local instance] HasDerivedCategory.standard

variable {R R' : CommRingCat.{u}} (φ : R ⟶ R')

/-- Relative sections of a scheme over `Spec R'`, with scalars restricted to `R`,
are relative sections of the same scheme regarded over `Spec R`. -/
abbrev overMapSectionsIso (X : Over (Spec R')) :
    relativeGlobalSections X.hom ⋙ ModuleCat.restrictScalars φ.hom ≅
      relativeGlobalSections ((Over.map (Spec.map φ)).obj X).hom :=
  relativeGlobalSectionsBaseRingIso φ ((Over.map (Spec.map φ)).obj X).hom X.hom rfl

variable {X Y : Over (Spec R')} (h : Y ⟶ X)

/-- The pushforward-sections identification commutes with scalar restriction. -/
lemma overMapSectionsIso_pushforwardSections (N : Y.left.Modules) :
    (overMapSectionsIso φ X).hom.app ((Scheme.Modules.pushforward h.left).obj N) ≫
        (relativePushforwardSectionsIso ((Over.map (Spec.map φ)).map h)).hom.app N =
      (ModuleCat.restrictScalars φ.hom).map ((relativePushforwardSectionsIso h).hom.app N) ≫
        (overMapSectionsIso φ Y).hom.app N := by
  ext x
  rfl

/-- The termwise comparison commutes with the pushforward-sections complexes. -/
lemma plusTermwiseIso_hom_pullbackSectionsComplexIso (K : CochainComplex.Plus Y.left.Modules) :
    (DerivedPlus.plusTermwiseIso (relativeGlobalSections X.hom)
        (ModuleCat.restrictScalars φ.hom) (overMapSectionsIso φ X)).hom.app
        ((Scheme.Modules.pushforward h.left).mapCochainComplexPlus.obj K) ≫
      DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map
        (pullbackSectionsComplexIso ((Over.map (Spec.map φ)).map h) K).hom) =
    (ModuleCat.restrictScalars φ.hom).mapDerivedCategory.map (DerivedCategory.Plus.ι.map
        (DerivedCategory.Plus.Q.map (pullbackSectionsComplexIso h K).hom)) ≫
      (DerivedPlus.plusTermwiseIso (relativeGlobalSections Y.hom)
        (ModuleCat.restrictScalars φ.hom) (overMapSectionsIso φ Y)).hom.app K := by
  have hc : (Functor.mapHomologicalComplexCompIso (overMapSectionsIso φ X)
        (ComplexShape.up ℤ)).hom.app
        ((Scheme.Modules.pushforward h.left).mapCochainComplexPlus.obj K).obj ≫
      (CochainComplex.Plus.ι _).map
        (pullbackSectionsComplexIso ((Over.map (Spec.map φ)).map h) K).hom =
    ((ModuleCat.restrictScalars φ.hom).mapHomologicalComplex _).map
        ((CochainComplex.Plus.ι _).map (pullbackSectionsComplexIso h K).hom) ≫
      (Functor.mapHomologicalComplexCompIso (overMapSectionsIso φ Y) (ComplexShape.up ℤ)).hom.app
        K.obj := by
    simp only [pullbackSectionsComplexIso, Functor.preimageIso_hom, Functor.map_preimage]
    ext i : 1
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplexCompIso_hom_app_f,
      Functor.mapHomologicalComplex_map_f]
    exact overMapSectionsIso_pushforwardSections φ h (K.obj.X i)
  have hf : (ModuleCat.restrictScalars φ.hom).mapDerivedCategory.map
        (DerivedCategory.Q.map ((CochainComplex.Plus.ι _).map (pullbackSectionsComplexIso h K).hom)) ≫
      (ModuleCat.restrictScalars φ.hom).mapDerivedCategoryFactors.hom.app
        (((relativeGlobalSections Y.hom).mapHomologicalComplex _).obj K.obj) =
    (ModuleCat.restrictScalars φ.hom).mapDerivedCategoryFactors.hom.app
        (((relativeGlobalSections X.hom).mapHomologicalComplex _).obj
          ((Scheme.Modules.pushforward h.left).mapCochainComplexPlus.obj K).obj) ≫
      DerivedCategory.Q.map (((ModuleCat.restrictScalars φ.hom).mapHomologicalComplex _).map
        ((CochainComplex.Plus.ι _).map (pullbackSectionsComplexIso h K).hom)) :=
    (ModuleCat.restrictScalars φ.hom).mapDerivedCategoryFactors.hom.naturality _
  have k₁ : DerivedCategory.Plus.ι.map
        (DerivedCategory.Plus.Q.map (pullbackSectionsComplexIso h K).hom) ≫
      (DerivedCategory.Plus.QCompιIso _).hom.app
        ((relativeGlobalSections Y.hom).mapCochainComplexPlus.obj K) =
    (DerivedCategory.Plus.QCompιIso _).hom.app
        ((relativeGlobalSections X.hom).mapCochainComplexPlus.obj
          ((Scheme.Modules.pushforward h.left).mapCochainComplexPlus.obj K)) ≫
      DerivedCategory.Q.map ((CochainComplex.Plus.ι _).map (pullbackSectionsComplexIso h K).hom) :=
    (DerivedCategory.Plus.QCompιIso _).hom.naturality _
  have k₂ : DerivedCategory.Q.map ((CochainComplex.Plus.ι _).map
        (pullbackSectionsComplexIso ((Over.map (Spec.map φ)).map h) K).hom) ≫
      (DerivedCategory.Plus.QCompιIso _).inv.app
        ((relativeGlobalSections ((Over.map (Spec.map φ)).obj Y).hom).mapCochainComplexPlus.obj K) =
    (DerivedCategory.Plus.QCompιIso _).inv.app
        ((relativeGlobalSections ((Over.map (Spec.map φ)).obj X).hom).mapCochainComplexPlus.obj
          ((Scheme.Modules.pushforward h.left).mapCochainComplexPlus.obj K)) ≫
      DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map
        (pullbackSectionsComplexIso ((Over.map (Spec.map φ)).map h) K).hom) :=
    (DerivedCategory.Plus.QCompιIso _).inv.naturality _
  simp only [DerivedPlus.plusTermwiseIso, NatIso.ofComponents_hom_app, Iso.trans_hom,
    Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv, Category.assoc]
  rw [← k₂, ← Functor.map_comp_assoc DerivedCategory.Q, hc, Functor.map_comp_assoc,
    ← Functor.map_comp_assoc (ModuleCat.restrictScalars φ.hom).mapDerivedCategory, k₁,
    Functor.map_comp_assoc, reassoc_of% hf]

/-- Inverse form of `plusTermwiseIso_hom_pullbackSectionsComplexIso`. -/
@[reassoc]
lemma pullbackSectionsComplexIso_plusTermwiseIso_inv (K : CochainComplex.Plus Y.left.Modules) :
    DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map
        (pullbackSectionsComplexIso ((Over.map (Spec.map φ)).map h) K).hom) ≫
      (DerivedPlus.plusTermwiseIso (relativeGlobalSections Y.hom)
        (ModuleCat.restrictScalars φ.hom) (overMapSectionsIso φ Y)).inv.app K =
    (DerivedPlus.plusTermwiseIso (relativeGlobalSections X.hom)
        (ModuleCat.restrictScalars φ.hom) (overMapSectionsIso φ X)).inv.app
        ((Scheme.Modules.pushforward h.left).mapCochainComplexPlus.obj K) ≫
      (ModuleCat.restrictScalars φ.hom).mapDerivedCategory.map (DerivedCategory.Plus.ι.map
        (DerivedCategory.Plus.Q.map (pullbackSectionsComplexIso h K).hom)) := by
  rw [← cancel_epi ((DerivedPlus.plusTermwiseIso (relativeGlobalSections X.hom)
        (ModuleCat.restrictScalars φ.hom) (overMapSectionsIso φ X)).hom.app
        ((Scheme.Modules.pushforward h.left).mapCochainComplexPlus.obj K)),
    Iso.hom_inv_id_app_assoc, reassoc_of% (plusTermwiseIso_hom_pullbackSectionsComplexIso φ h K),
    Iso.hom_inv_id_app]
  exact Category.comp_id _

/-- Derived form: the canonical derived pullback commutes with scalar restriction. -/
lemma relativeDerivedSectionsPullback_overMap (M : X.left.Modules) :
    DerivedCategory.Plus.ι.map
        (relativeDerivedSectionsPullback ((Over.map (Spec.map φ)).map h) M) ≫
        (DerivedPlus.derivedCompIso (relativeGlobalSections Y.hom)
          (ModuleCat.restrictScalars φ.hom) (overMapSectionsIso φ Y)).inv.app
          ((Scheme.Modules.pullback h.left).obj M) =
      (DerivedPlus.derivedCompIso (relativeGlobalSections X.hom)
          (ModuleCat.restrictScalars φ.hom) (overMapSectionsIso φ X)).inv.app M ≫
        (ModuleCat.restrictScalars φ.hom).mapDerivedCategory.map
          (DerivedCategory.Plus.ι.map (relativeDerivedSectionsPullback h M)) := by
  rw [← DerivedPlus.baseChangeTrans_single, ← DerivedPlus.baseChangeTrans_single]
  have hu₀ : IsIso ((relativeGlobalSections
      ((Over.map (Spec.map φ)).obj X).hom).rightDerivedFunctorPlusUnit.app
        ((Scheme.Modules.pushforward h.left).mapCochainComplexPlus.obj
          (DerivedPlus.resolutionPlus
            (injectiveResolution ((Scheme.Modules.pullback h.left).obj M))))) :=
    isIso_unit_pushforward_resolution ((Over.map (Spec.map φ)).map h) M
  have hu : IsIso ((relativeGlobalSections X.hom).rightDerivedFunctorPlusUnit.app
        ((Scheme.Modules.pushforward h.left).mapCochainComplexPlus.obj
          (DerivedPlus.resolutionPlus
            (injectiveResolution ((Scheme.Modules.pullback h.left).obj M))))) :=
    isIso_unit_pushforward_resolution h M
  have h₄ := (DerivedPlus.baseChangeTrans (relativeGlobalSections X.hom)
    (ModuleCat.restrictScalars φ.hom) (overMapSectionsIso φ X)).naturality
      (pullbackDerivedAugmentation ((Over.map (Spec.map φ)).map h) M)
  simp only [Functor.comp_map] at h₄
  simp only [relativeDerivedSectionsPullback, Functor.map_comp, Category.assoc]
  dsimp only [Over.map_map_left, Over.map_obj_left] at h₄ ⊢
  rw [DerivedPlus.derivedComplexIso_inv_baseChangeTrans,
    pullbackSectionsComplexIso_plusTermwiseIso_inv_assoc,
    DerivedPlus.inv_unit_comp_plusTermwiseIso_inv_assoc, reassoc_of% h₄]
  rfl

/-- The canonical cohomology pullback of schemes over `Spec R'` is compatible
with the identification of their `R`-module cohomology with scalar restriction. -/
theorem relativeCohomologyPullback_overMap (M : X.left.Modules) (n : ℕ) :
    relativeCohomologyPullback ((Over.map (Spec.map φ)).map h) M n ≫
        (relativeCohomologyBaseRingIso φ ((Over.map (Spec.map φ)).obj Y).hom Y.hom rfl n).hom.app
          ((Scheme.Modules.pullback h.left).obj M) =
      (relativeCohomologyBaseRingIso φ ((Over.map (Spec.map φ)).obj X).hom X.hom rfl n).hom.app M ≫
        (ModuleCat.restrictScalars φ.hom).map (relativeCohomologyPullback h M n) := by
  have hD := relativeDerivedSectionsPullback_overMap φ h M
  have hX := DerivedPlus.derivedCompIso_inv_homology (relativeGlobalSections X.hom)
    (ModuleCat.restrictScalars φ.hom) (overMapSectionsIso φ X) (injectiveResolution M) n
  have hY := DerivedPlus.derivedCompIso_inv_homology (relativeGlobalSections Y.hom)
    (ModuleCat.restrictScalars φ.hom) (overMapSectionsIso φ Y)
    (injectiveResolution ((Scheme.Modules.pullback h.left).obj M)) n
  have bX : (DerivedPlus.rightDerivedCompIsoOfResolution (relativeGlobalSections X.hom)
      (ModuleCat.restrictScalars φ.hom) (overMapSectionsIso φ X) (injectiveResolution M) n).inv =
      (relativeCohomologyBaseRingIso φ ((Over.map (Spec.map φ)).obj X).hom X.hom rfl n).hom.app
        M := by
    rw [rightDerivedCompIsoOfResolution_baseRingIso]
    rfl
  have bY : (DerivedPlus.rightDerivedCompIsoOfResolution (relativeGlobalSections Y.hom)
      (ModuleCat.restrictScalars φ.hom) (overMapSectionsIso φ Y)
      (injectiveResolution ((Scheme.Modules.pullback h.left).obj M)) n).inv =
      (relativeCohomologyBaseRingIso φ ((Over.map (Spec.map φ)).obj Y).hom Y.hom rfl n).hom.app
        ((Scheme.Modules.pullback h.left).obj M) := by
    rw [rightDerivedCompIsoOfResolution_baseRingIso]
    rfl
  have e₀ : (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) n).map
      (relativeDerivedSectionsPullback ((Over.map (Spec.map φ)).map h) M) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).map
        (DerivedCategory.Plus.ι.map
          (relativeDerivedSectionsPullback ((Over.map (Spec.map φ)).map h) M)) := rfl
  have e₁ : (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R') n).map
      (relativeDerivedSectionsPullback h M) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
        (DerivedCategory.Plus.ι.map (relativeDerivedSectionsPullback h M)) := rfl
  rw [← bX, ← bY]
  simp only [relativeCohomologyPullback, Category.assoc]
  dsimp only [Over.map_map_left, Over.map_obj_left] at hD hX hY e₀ ⊢
  rw [← hY, e₀, ← Functor.map_comp_assoc, hD, Functor.map_comp_assoc]
  erw [DerivedPlus.mapDerivedCategoryHomologyIso_hom_naturality_assoc]
  rw [← cancel_epi (DerivedPlus.homologyIso
      (relativeGlobalSections ((Over.map (Spec.map φ)).obj X).hom) (injectiveResolution M) n).hom,
    Iso.hom_inv_id_assoc, ← reassoc_of% hX, e₁]
  simp only [Functor.map_comp, Iso.map_hom_inv_id_assoc]
  rfl

end Langlands.AlgebraicGeometry.Modules.DerivedSections
