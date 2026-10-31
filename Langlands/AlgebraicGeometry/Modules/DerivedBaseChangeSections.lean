import Langlands.AlgebraicGeometry.Modules.DerivedBaseChangeResolution

/-! # Derived base change on the explicit complex of sections -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Cohomology Langlands.Cohomology.AcyclicResolution

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

attribute [local instance] HasDerivedCategory.standard

section Sections

variable {X : Scheme.{u}} {R : CommRingCat.{u}} (f : X ⟶ Spec R)
  {M : X.Modules} {K : CochainComplex X.Modules ℕ}
  (ε : (CochainComplex.single₀ X.Modules).obj M ⟶ K) [QuasiIso ε]

/-- The canonical derived comparison whose source is the integer extension
of the actual natural-indexed sections complex. -/
def resolutionSectionsDerivedComparison :
    DerivedCategory.Q.obj
        ((((relativeGlobalSections f).mapHomologicalComplex _).obj K).extend
          ComplexShape.embeddingUpNat) ⟶
      (DerivedPlus.derivedComplex (relativeGlobalSections f) ⋙
        DerivedCategory.Plus.ι).obj M :=
  DerivedCategory.Q.map
      (DerivedPlus.mapExtendIso (relativeGlobalSections f) K
        ComplexShape.embeddingUpNat).hom ≫
    derivedResolutionComparison (relativeGlobalSections f) ε

end Sections

section BaseChange

variable {X Y : Scheme.{u}} {R S : CommRingCat.{u}}
  (φ : R ⟶ S) (f : X ⟶ Spec R) (f' : Y ⟶ Spec S)
  (g : Y ⟶ X) (w : g ≫ f = f' ≫ Spec.map φ)
  {K : CochainComplex X.Modules ℕ} {L : CochainComplex Y.Modules ℕ}

/-- The canonical comparison between scalar restriction in the derived
category and the extension of scalar restriction of a sections complex. -/
def sectionsRestrictScalarsIso (C : CochainComplex (ModuleCat.{u} S) ℕ) :
    (ModuleCat.restrictScalars φ.hom).mapDerivedCategory.obj
        (DerivedCategory.Q.obj (C.extend ComplexShape.embeddingUpNat)) ≅
      DerivedCategory.Q.obj
        ((((ModuleCat.restrictScalars φ.hom).mapHomologicalComplex _).obj C).extend
          ComplexShape.embeddingUpNat) :=
  (ModuleCat.restrictScalars φ.hom).mapDerivedCategoryFactors.app
      (C.extend ComplexShape.embeddingUpNat) ≪≫
    DerivedCategory.Q.mapIso
      (extendMapIso ComplexShape.embeddingUpNat (ModuleCat.restrictScalars φ.hom) C)

/-- Localize the integer extension of the actual semilinear sections map,
then use the specified scalar-restriction comparison. -/
def derivedSectionsBaseChangeMap
    (t : K ⟶ ((Scheme.Modules.pushforward g).mapHomologicalComplex _).obj L) :
    DerivedCategory.Q.obj
        ((((relativeGlobalSections f).mapHomologicalComplex _).obj K).extend
          ComplexShape.embeddingUpNat) ⟶
      (ModuleCat.restrictScalars φ.hom).mapDerivedCategory.obj
        (DerivedCategory.Q.obj
          ((((relativeGlobalSections f').mapHomologicalComplex _).obj L).extend
            ComplexShape.embeddingUpNat)) :=
  DerivedCategory.Q.map
      (HomologicalComplex.extendMap
        (resolutionSectionsBaseChangeMap φ f f' g w t) ComplexShape.embeddingUpNat) ≫
    (sectionsRestrictScalarsIso φ
      (((relativeGlobalSections f').mapHomologicalComplex _).obj L)).inv

private lemma extend_pushforward_comparison
    (t : K ⟶ ((Scheme.Modules.pushforward g).mapHomologicalComplex _).obj L) :
    (DerivedPlus.mapExtendIso (relativeGlobalSections f) K
        ComplexShape.embeddingUpNat).hom ≫
      ((relativeGlobalSections f).mapHomologicalComplex _).map
        (HomologicalComplex.extendMap t ComplexShape.embeddingUpNat) ≫
      (compResolutionIso (relativeGlobalSections f)
        (relativeGlobalSectionsCompIso g f) L).inv =
    HomologicalComplex.extendMap
        (((relativeGlobalSections f).mapHomologicalComplex _).map t ≫
          (Functor.mapHomologicalComplexCompIso
            (relativeGlobalSectionsCompIso g f) _).hom.app L)
        ComplexShape.embeddingUpNat ≫
      (DerivedPlus.mapExtendIso (relativeGlobalSections (g ≫ f)) L
        ComplexShape.embeddingUpNat).hom := by
  rw [DerivedPlus.mapExtendIso_hom_naturality_assoc]
  simp only [compResolutionIso, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv,
    Iso.app_hom, Category.assoc, Iso.hom_inv_id_assoc,
    HomologicalComplex.extendMap_comp, ComplexShape.Embedding.extendFunctor_map]

private lemma extend_baseRing_comparison :
    (DerivedPlus.mapExtendIso (relativeGlobalSections (g ≫ f)) L
        ComplexShape.embeddingUpNat).hom ≫
      (Functor.mapHomologicalComplexCompIso
        (relativeGlobalSectionsBaseRingIso φ (g ≫ f) f' w) _).inv.app
          (L.extend ComplexShape.embeddingUpNat) =
    HomologicalComplex.extendMap
        ((Functor.mapHomologicalComplexCompIso
          (relativeGlobalSectionsBaseRingIso φ (g ≫ f) f' w) _).inv.app L)
        ComplexShape.embeddingUpNat ≫
      (DerivedPlus.mapExtendIso (ModuleCat.restrictScalars φ.hom)
        (((relativeGlobalSections f').mapHomologicalComplex _).obj L)
        ComplexShape.embeddingUpNat).hom ≫
      ((ModuleCat.restrictScalars φ.hom).mapHomologicalComplex _).map
        (DerivedPlus.mapExtendIso (relativeGlobalSections f') L
          ComplexShape.embeddingUpNat).hom := by
  let e := relativeGlobalSectionsBaseRingIso φ (g ≫ f) f' w
  let eZ := (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).app
    (L.extend ComplexShape.embeddingUpNat)
  let eN := (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℕ)).app L
  let mH := DerivedPlus.mapExtendIso (relativeGlobalSections (g ≫ f)) L
    ComplexShape.embeddingUpNat
  let mG := DerivedPlus.mapExtendIso (relativeGlobalSections f') L
    ComplexShape.embeddingUpNat
  let mP := DerivedPlus.mapExtendIso (ModuleCat.restrictScalars φ.hom)
    (((relativeGlobalSections f').mapHomologicalComplex _).obj L)
    ComplexShape.embeddingUpNat
  have he : eZ ≪≫ mH.symm =
      ((ModuleCat.restrictScalars φ.hom).mapHomologicalComplex _).mapIso mG.symm ≪≫
        mP.symm ≪≫ (ComplexShape.embeddingUpNat.extendFunctor _).mapIso eN := by
    apply Iso.ext
    exact DerivedPlus.mapHomologicalComplexCompIso_hom_app_extend_comp
      (relativeGlobalSections f') (ModuleCat.restrictScalars φ.hom) e L
  simpa only [eZ, eN, mH, mG, mP, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv, Iso.app_inv, ComplexShape.Embedding.extendFunctor_map,
    Category.assoc] using congrArg Iso.inv he

private lemma postcomp_inv_formula :
    (derivedResolutionPostcompIso (relativeGlobalSections f')
      (ModuleCat.restrictScalars φ.hom)
      (relativeGlobalSectionsBaseRingIso φ (g ≫ f) f' w) L).inv =
    DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso
          (relativeGlobalSectionsBaseRingIso φ (g ≫ f) f' w) _).inv.app
            (L.extend ComplexShape.embeddingUpNat)) ≫
      (ModuleCat.restrictScalars φ.hom).mapDerivedCategoryFactors.inv.app
        (((relativeGlobalSections f').mapHomologicalComplex _).obj
          (L.extend ComplexShape.embeddingUpNat)) := by
  have he :
      derivedResolutionPostcompIso (relativeGlobalSections f')
        (ModuleCat.restrictScalars φ.hom)
        (relativeGlobalSectionsBaseRingIso φ (g ≫ f) f' w) L =
      (ModuleCat.restrictScalars φ.hom).mapDerivedCategoryFactors.app
          (((relativeGlobalSections f').mapHomologicalComplex _).obj
            (L.extend ComplexShape.embeddingUpNat)) ≪≫
        DerivedCategory.Q.mapIso
          ((Functor.mapHomologicalComplexCompIso
            (relativeGlobalSectionsBaseRingIso φ (g ≫ f) f' w) _).app
              (L.extend ComplexShape.embeddingUpNat)) := by
    apply Iso.ext
    exact DerivedPlus.resolutionPostcompNatIso_hom_app_comp_resolutionCongrNatIso_hom_app
      (relativeGlobalSections f') (ModuleCat.restrictScalars φ.hom)
      (relativeGlobalSectionsBaseRingIso φ (g ≫ f) f' w) L
  simpa only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv] using congrArg Iso.inv he

/-- The map on sections complexes is the same as the map on sections of
extended complexes, through the specified extension comparisons. -/
@[reassoc]
lemma derivedSectionsBaseChangeMap_comparison
    (t : K ⟶ ((Scheme.Modules.pushforward g).mapHomologicalComplex _).obj L) :
    DerivedCategory.Q.map
        (DerivedPlus.mapExtendIso (relativeGlobalSections f) K
          ComplexShape.embeddingUpNat).hom ≫
      derivedResolutionBaseChangeMap φ f f' g w t =
    derivedSectionsBaseChangeMap φ f f' g w t ≫
      (ModuleCat.restrictScalars φ.hom).mapDerivedCategory.map
        (DerivedCategory.Q.map
          (DerivedPlus.mapExtendIso (relativeGlobalSections f') L
            ComplexShape.embeddingUpNat).hom) := by
  have hn := (ModuleCat.restrictScalars φ.hom).mapDerivedCategoryFactors.inv.naturality
    (DerivedPlus.mapExtendIso (relativeGlobalSections f') L
      ComplexShape.embeddingUpNat).hom
  simp only [Functor.comp_map] at hn
  simp only [derivedResolutionBaseChangeMap, derivedResolutionFunctor,
    derivedCompResolutionIso, Functor.comp_map, Functor.mapIso_inv,
    ComplexShape.Embedding.extendFunctor_map]
  rw [← DerivedCategory.Q.map_comp_assoc, ← DerivedCategory.Q.map_comp_assoc,
    Category.assoc, extend_pushforward_comparison, DerivedCategory.Q.map_comp]
  rw [postcomp_inv_formula]
  simp only [Category.assoc]
  rw [← DerivedCategory.Q.map_comp_assoc
      (DerivedPlus.mapExtendIso (relativeGlobalSections (g ≫ f)) L
        ComplexShape.embeddingUpNat).hom,
    extend_baseRing_comparison, DerivedCategory.Q.map_comp, DerivedCategory.Q.map_comp]
  simp only [Category.assoc]
  rw [hn]
  simp only [derivedSectionsBaseChangeMap, resolutionSectionsBaseChangeMap,
    sectionsRestrictScalarsIso, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv,
    extendMapIso, Iso.symm_inv, HomologicalComplex.extendMap_comp,
    Functor.map_comp, Category.assoc]

variable {M : X.Modules}
  (ε : (CochainComplex.single₀ X.Modules).obj M ⟶ K) [QuasiIso ε]
  (η : (CochainComplex.single₀ Y.Modules).obj ((Scheme.Modules.pullback g).obj M) ⟶ L)
  [QuasiIso η]
  [QuasiIso (mapResolutionAugmentation (Scheme.Modules.pushforward g) η)]
  (t : K ⟶ ((Scheme.Modules.pushforward g).mapHomologicalComplex _).obj L)
  (ht : ε ≫ t =
    (CochainComplex.single₀ X.Modules).map
        ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M) ≫
      mapResolutionAugmentation (Scheme.Modules.pushforward g) η)

include ht in
/-- The actual semilinear cochain map on sections computes the actual
derived base-change morphism through the canonical resolution comparisons. -/
@[reassoc]
theorem resolutionSectionsDerivedComparison_baseChangeMap
    (hM : ∀ q : ℕ, IsZero ((higherDirectImage g (q + 1)).obj
      ((Scheme.Modules.pullback g).obj M))) :
    resolutionSectionsDerivedComparison f ε ≫
        derivedBaseChangeMap φ f f' g w M hM =
      derivedSectionsBaseChangeMap φ f f' g w t ≫
        (ModuleCat.restrictScalars φ.hom).mapDerivedCategory.map
          (resolutionSectionsDerivedComparison f' η) := by
  simp only [resolutionSectionsDerivedComparison, Category.assoc]
  rw [derivedResolutionComparison_baseChangeMap φ f f' g w ε η t ht hM,
    derivedSectionsBaseChangeMap_comparison_assoc]
  simp only [Functor.map_comp]

end BaseChange

end Langlands.AlgebraicGeometry.Modules.DerivedSections
