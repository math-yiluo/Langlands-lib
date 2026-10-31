import Langlands.AlgebraicGeometry.Modules.CechResolution.DerivedComparison
import Langlands.AlgebraicGeometry.Modules.CechResolution.SectionsBaseChange
import Langlands.AlgebraicGeometry.Modules.CechResolution.Pushforward
import Langlands.AlgebraicGeometry.Modules.DerivedBaseChangeSections

/-! # Actual derived base change through alternating Čech cochains -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Cohomology Langlands.Cohomology.AcyclicResolution
open Langlands.AlgebraicGeometry.Modules.DerivedSections

namespace Langlands.AlgebraicGeometry.Modules.CechResolution

attribute [local instance] HasDerivedCategory.standard

variable {X Y : Scheme.{u}} {R S : CommRingCat.{u}}
  (φ : R ⟶ S) (f : X ⟶ Spec R) (f' : Y ⟶ Spec S)
  (g : Y ⟶ X) (w : g ≫ f = f' ≫ Spec.map φ)
  [IsAffineHom g] {M : X.Modules} {N : Y.Modules}
  (a : M ⟶ (Scheme.Modules.pushforward g).obj N)
  (𝒰 : X.OrderedAffineCover)

/-- The actual scalar-linear Čech sections map, transported to alternating
Čech cochains by the specified sections-complex isomorphisms. -/
def scalarCechCochainMap :
    ((ModuleCat.extendScalars φ.hom).mapHomologicalComplex _).obj
        (cechCochainComplex f 𝒰 M) ⟶
      cechCochainComplex f' (inverseImageCover g 𝒰) N :=
  ((ModuleCat.extendScalars φ.hom).mapHomologicalComplex _).map
      (sectionsComplexIso f 𝒰 M).inv ≫
    scalarCechSectionsMap φ f f' g w a 𝒰 ≫
      (sectionsComplexIso f' (inverseImageCover g 𝒰) N).hom

/-- The actual semilinear map between alternating Čech cochain complexes. -/
def cechCochainSectionsMap :
    cechCochainComplex f 𝒰 M ⟶
      ((ModuleCat.restrictScalars φ.hom).mapHomologicalComplex _).obj
        (cechCochainComplex f' (inverseImageCover g 𝒰) N) :=
  (sectionsComplexIso f 𝒰 M).inv ≫
    resolutionSectionsBaseChangeMap φ f f' g w (cechPushforward g a 𝒰) ≫
      ((ModuleCat.restrictScalars φ.hom).mapHomologicalComplex _).map
        (sectionsComplexIso f' (inverseImageCover g 𝒰) N).hom

/-- The semilinear cochain map is the actual adjunct of the scalar-linear
cochain map, for every base-ring homomorphism. -/
lemma cechCochainSectionsMap_eq_adjunct :
    cechCochainSectionsMap φ f f' g w a 𝒰 =
      ((extendRestrictScalarsComplexAdjunction (ComplexShape.up ℕ) φ.hom).homEquiv _ _)
        (scalarCechCochainMap φ f f' g w a 𝒰) := by
  rw [scalarCechCochainMap, Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right]
  simp only [scalarCechSectionsMap, scalarResolutionSectionsBaseChangeMap, Equiv.apply_symm_apply,
    cechCochainSectionsMap]

omit [IsAffineHom g] in
private lemma sectionsRestrictScalarsIso_inv_naturality
    {C D : CochainComplex (ModuleCat.{u} S) ℕ} (b : C ⟶ D) :
    DerivedCategory.Q.map
        (HomologicalComplex.extendMap
          (((ModuleCat.restrictScalars φ.hom).mapHomologicalComplex _).map b)
          ComplexShape.embeddingUpNat) ≫
      (sectionsRestrictScalarsIso φ D).inv =
    (sectionsRestrictScalarsIso φ C).inv ≫
      (ModuleCat.restrictScalars φ.hom).mapDerivedCategory.map
        (DerivedCategory.Q.map
          (HomologicalComplex.extendMap b ComplexShape.embeddingUpNat)) := by
  have he := DerivedPlus.mapExtendIso_hom_naturality
    (ModuleCat.restrictScalars φ.hom) ComplexShape.embeddingUpNat b
  have hn := (ModuleCat.restrictScalars φ.hom).mapDerivedCategoryFactors.inv.naturality
    (HomologicalComplex.extendMap b ComplexShape.embeddingUpNat)
  simp only [Functor.comp_map] at hn
  simp only [sectionsRestrictScalarsIso, Iso.trans_inv, Functor.mapIso_inv,
    Iso.app_inv, extendMapIso, Iso.symm_inv, Category.assoc]
  rw [← DerivedCategory.Q.map_comp_assoc, ← he,
    DerivedCategory.Q.map_comp_assoc, hn]

/-- Localize the integer extension of the actual semilinear alternating
Čech cochain map induced by the pullback unit. -/
def cechDerivedBaseChangeMap :
    DerivedCategory.Q.obj
        ((cechCochainComplex f 𝒰 M).extend ComplexShape.embeddingUpNat) ⟶
      (ModuleCat.restrictScalars φ.hom).mapDerivedCategory.obj
        (DerivedCategory.Q.obj
          ((cechCochainComplex f' (inverseImageCover g 𝒰)
            ((Scheme.Modules.pullback g).obj M)).extend ComplexShape.embeddingUpNat)) :=
  DerivedCategory.Q.map
      (HomologicalComplex.extendMap
        (cechCochainSectionsMap φ f f' g w
          ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M) 𝒰)
        ComplexShape.embeddingUpNat) ≫
    (sectionsRestrictScalarsIso φ
      (cechCochainComplex f' (inverseImageCover g 𝒰)
        ((Scheme.Modules.pullback g).obj M))).inv

/-- The specified alternating-cochain morphism is the actual sections
morphism transported by the two sections-complex isomorphisms. -/
lemma cechDerivedBaseChangeMap_eq_transport :
    cechDerivedBaseChangeMap φ f f' g w (M := M) 𝒰 =
      DerivedCategory.Q.map
          (HomologicalComplex.extendMap (sectionsComplexIso f 𝒰 M).inv
            ComplexShape.embeddingUpNat) ≫
        derivedSectionsBaseChangeMap φ f f' g w (cechPullback g (M := M) 𝒰) ≫
          (ModuleCat.restrictScalars φ.hom).mapDerivedCategory.map
            (DerivedCategory.Q.map
              (HomologicalComplex.extendMap
                (sectionsComplexIso f' (inverseImageCover g 𝒰)
                  ((Scheme.Modules.pullback g).obj M)).hom
                ComplexShape.embeddingUpNat)) := by
  simp only [cechDerivedBaseChangeMap, cechCochainSectionsMap,
    HomologicalComplex.extendMap_comp, Functor.map_comp, Category.assoc]
  rw [sectionsRestrictScalarsIso_inv_naturality]
  simp only [derivedSectionsBaseChangeMap, cechPullback, Category.assoc,
    CategoryTheory.Functor.id_obj]

/-- The actual Čech sections map computes the actual derived base-change
morphism for every base-ring map. -/
@[reassoc]
theorem cechSectionsDerivedComparison_baseChange
    (hM : ∀ q : ℕ, IsZero ((higherDirectImage g (q + 1)).obj
      ((Scheme.Modules.pullback g).obj M))) :
    cechSectionsDerivedComparison f 𝒰 M ≫
        derivedBaseChangeMap φ f f' g w M hM =
      derivedSectionsBaseChangeMap φ f f' g w (cechPullback g (M := M) 𝒰) ≫
        (ModuleCat.restrictScalars φ.hom).mapDerivedCategory.map
          (cechSectionsDerivedComparison f' (inverseImageCover g 𝒰)
            ((Scheme.Modules.pullback g).obj M)) := by
  let := quasiIso_cechAug 𝒰 M
  let := quasiIso_cechAug (inverseImageCover g 𝒰) ((Scheme.Modules.pullback g).obj M)
  let := quasiIso_pushforward_cechAug g ((Scheme.Modules.pullback g).obj M) 𝒰
  simpa only [cechSectionsDerivedComparison, resolutionSectionsDerivedComparison,
    extendMapIso, Iso.symm_inv] using
    resolutionSectionsDerivedComparison_baseChangeMap φ f f' g w
      (cechAug 𝒰 M)
      (cechAug (inverseImageCover g 𝒰) ((Scheme.Modules.pullback g).obj M))
      (cechPullback g 𝒰) (cechAug_cechPullback g 𝒰) hM

/-- The named canonical comparison from alternating Čech cochains
intertwines the actual semilinear cochain map and actual derived base change. -/
@[reassoc]
theorem cechDerivedComparison_baseChange
    (hM : ∀ q : ℕ, IsZero ((higherDirectImage g (q + 1)).obj
      ((Scheme.Modules.pullback g).obj M))) :
    cechDerivedComparison f 𝒰 M ≫
        derivedBaseChangeMap φ f f' g w M hM =
      cechDerivedBaseChangeMap φ f f' g w (M := M) 𝒰 ≫
        (ModuleCat.restrictScalars φ.hom).mapDerivedCategory.map
          (cechDerivedComparison f' (inverseImageCover g 𝒰)
            ((Scheme.Modules.pullback g).obj M)) := by
  rw [cechDerivedBaseChangeMap_eq_transport]
  simp only [cechDerivedComparison, Functor.map_comp, Category.assoc,
    ComplexShape.Embedding.extendFunctor_map]
  rw [cechSectionsDerivedComparison_baseChange]
  rw [← Functor.map_comp_assoc, ← DerivedCategory.Q.map_comp,
    ← HomologicalComplex.extendMap_comp, Iso.hom_inv_id,
    HomologicalComplex.extendMap_id]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]

end Langlands.AlgebraicGeometry.Modules.CechResolution
