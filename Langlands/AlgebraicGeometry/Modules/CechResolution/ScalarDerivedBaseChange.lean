import Langlands.AlgebraicGeometry.Modules.CechResolution.DerivedBaseChange
import Langlands.AlgebraicGeometry.Modules.PerfectModelRestriction

/-! # Scalar Čech maps compute base change of perfect models -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Cohomology Langlands.Cohomology.ModuleComplex
open Langlands.AlgebraicGeometry.Modules.DerivedSections
open Langlands.AlgebraicGeometry.Picard

namespace Langlands.AlgebraicGeometry.Modules.CechResolution

attribute [local instance] HasDerivedCategory.standard

section Scalars

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

private lemma extend_scalar_adjunct
    (C : CochainComplex (ModuleCat.{u} R) ℕ)
    (D : CochainComplex (ModuleCat.{u} S) ℕ)
    (b : ((ModuleCat.extendScalars φ.hom).mapHomologicalComplex _).obj C ⟶ D) :
    (complexAdjunction (ModuleCat.extendRestrictScalarsAdj φ.hom) (.up ℤ)).unit.app
        (C.extend ComplexShape.embeddingUpNat) ≫
      ((ModuleCat.restrictScalars φ.hom).mapHomologicalComplex _).map
        ((extendMapIso ComplexShape.embeddingUpNat (ModuleCat.extendScalars φ.hom) C).hom ≫
          HomologicalComplex.extendMap b ComplexShape.embeddingUpNat) =
    HomologicalComplex.extendMap
        ((extendRestrictScalarsComplexAdjunction (.up ℕ) φ.hom).homEquiv _ _ b)
        ComplexShape.embeddingUpNat ≫
      (extendMapIso ComplexShape.embeddingUpNat (ModuleCat.restrictScalars φ.hom) D).inv := by
  apply HomologicalComplex.hom_ext
  intro i
  change (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app
        (HomologicalComplex.extend.X C (ComplexShape.embeddingUpNat.r i)) ≫
      (ModuleCat.restrictScalars φ.hom).map
        ((DerivedPlus.extendXMapIso (ModuleCat.extendScalars φ.hom) C
            (ComplexShape.embeddingUpNat.r i)).inv ≫
          HomologicalComplex.extend.mapX b (ComplexShape.embeddingUpNat.r i)) =
    HomologicalComplex.extend.mapX
        ((extendRestrictScalarsComplexAdjunction (.up ℕ) φ.hom).homEquiv _ _ b)
        (ComplexShape.embeddingUpNat.r i) ≫
      (DerivedPlus.extendXMapIso (ModuleCat.restrictScalars φ.hom) D
        (ComplexShape.embeddingUpNat.r i)).hom
  cases ComplexShape.embeddingUpNat.r i with
  | none => exact (HomologicalComplex.extend.isZero_X C rfl).eq_of_src _ _
  | some n =>
    simp only [DerivedPlus.extendXMapIso, Iso.refl_inv, Iso.refl_hom, Category.comp_id]
    rfl

private lemma derivedUnit_scalar_extendMap
    (C : CochainComplex (ModuleCat.{u} R) ℕ)
    (D : CochainComplex (ModuleCat.{u} S) ℕ)
    (b : ((ModuleCat.extendScalars φ.hom).mapHomologicalComplex _).obj C ⟶ D) :
    derivedComplexAdjunctionUnit (ModuleCat.extendRestrictScalarsAdj φ.hom)
        (C.extend ComplexShape.embeddingUpNat) ≫
      (ModuleCat.restrictScalars φ.hom).mapDerivedCategory.map
        (DerivedCategory.Q.map
          ((extendMapIso ComplexShape.embeddingUpNat (ModuleCat.extendScalars φ.hom) C).hom ≫
            HomologicalComplex.extendMap b ComplexShape.embeddingUpNat)) =
    DerivedCategory.Q.map
        (HomologicalComplex.extendMap
          ((extendRestrictScalarsComplexAdjunction (.up ℕ) φ.hom).homEquiv _ _ b)
          ComplexShape.embeddingUpNat) ≫
      (sectionsRestrictScalarsIso φ D).inv := by
  have hn := (ModuleCat.restrictScalars φ.hom).mapDerivedCategoryFactors.inv.naturality
    ((extendMapIso ComplexShape.embeddingUpNat (ModuleCat.extendScalars φ.hom) C).hom ≫
      HomologicalComplex.extendMap b ComplexShape.embeddingUpNat)
  simp only [Functor.comp_map] at hn
  simp only [derivedComplexAdjunctionUnit, Category.assoc, ← hn]
  rw [← DerivedCategory.Q.map_comp_assoc, extend_scalar_adjunct]
  simp only [Functor.map_comp, sectionsRestrictScalarsIso, Iso.trans_inv,
    Functor.mapIso_inv, Iso.app_inv, Category.assoc]

end Scalars

section Cech

variable {X Y : Scheme.{u}} {R S : CommRingCat.{u}}
  (φ : R ⟶ S) (f : X ⟶ Spec R) (f' : Y ⟶ Spec S)
  (g : Y ⟶ X) (w : g ≫ f = f' ≫ Spec.map φ) [IsAffineHom g]
  (M : X.Modules) (𝒰 : X.OrderedAffineCover)

/-- Localize the actual scalar-linear map on integer-extended alternating Čech cochains. -/
def scalarCechDerivedBaseChangeMap :
    DerivedCategory.Q.obj
        ((baseChange φ.hom).obj
          ((cechCochainComplex f 𝒰 M).extend ComplexShape.embeddingUpNat)) ⟶
      DerivedCategory.Q.obj
        ((cechCochainComplex f' (inverseImageCover g 𝒰)
          ((Scheme.Modules.pullback g).obj M)).extend ComplexShape.embeddingUpNat) :=
  DerivedCategory.Q.map
    ((extendMapIso ComplexShape.embeddingUpNat (ModuleCat.extendScalars φ.hom)
        (cechCochainComplex f 𝒰 M)).hom ≫
      HomologicalComplex.extendMap
        (scalarCechCochainMap φ f f' g w
          ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M) 𝒰)
        ComplexShape.embeddingUpNat)

/-- The explicit semilinear derived map is the derived adjunct of the scalar Čech map,
without any perfectness assumption on the Čech complex. -/
lemma cechDerivedBaseChangeMap_eq_adjunct :
    cechDerivedBaseChangeMap φ f f' g w (M := M) 𝒰 =
      derivedComplexAdjunctionUnit (ModuleCat.extendRestrictScalarsAdj φ.hom)
          ((cechCochainComplex f 𝒰 M).extend ComplexShape.embeddingUpNat) ≫
        (ModuleCat.restrictScalars φ.hom).mapDerivedCategory.map
          (scalarCechDerivedBaseChangeMap φ f f' g w M 𝒰) := by
  rw [scalarCechDerivedBaseChangeMap, derivedUnit_scalar_extendMap]
  rw [← cechCochainSectionsMap_eq_adjunct]
  rfl

end Cech

section Pullback

variable {X Y : Scheme.{u}} {R S : CommRingCat.{u}}
  {φ : R ⟶ S} {f : X ⟶ Spec R} {f' : Y ⟶ Spec S} {g : Y ⟶ X}
  (hp : IsPullback g f' f (Spec.map φ)) (L : LineBundle X)
  (𝒰 : X.OrderedAffineCover) {K : CochainComplex (ModuleCat.{u} R) ℤ}

/-- The scalar extension of a chain map into Čech cochains, followed by the actual
scalar-linear Čech base-change map. -/
def cechBaseChangeCochainMap
    (v : K ⟶ (cechCochainComplex f 𝒰 L.obj).extend ComplexShape.embeddingUpNat) :
    letI := isAffineHom_of_isPullback_spec hp
    (baseChange φ.hom).obj K ⟶
      (cechCochainComplex f' (inverseImageCover g 𝒰)
        ((Scheme.Modules.pullback g).obj L.obj)).extend ComplexShape.embeddingUpNat := by
  letI := isAffineHom_of_isPullback_spec hp
  exact (baseChange φ.hom).map v ≫
    (extendMapIso ComplexShape.embeddingUpNat (ModuleCat.extendScalars φ.hom)
      (cechCochainComplex f 𝒰 L.obj)).hom ≫
    HomologicalComplex.extendMap
      (scalarCechCochainMap φ f f' g hp.w
        ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app L.obj) 𝒰)
      ComplexShape.embeddingUpNat

/-- The actual base change of a perfect model represented by a Čech chain map is computed
by the explicit scalar Čech chain map, for every ring homomorphism. -/
theorem perfectModelBaseChange_cechDerivedComparison
    (hK : IsStrictlyPerfect K)
    (v : K ⟶ (cechCochainComplex f 𝒰 L.obj).extend ComplexShape.embeddingUpNat) :
    letI := isAffineHom_of_isPullback_spec hp
    perfectModelBaseChange hp L hK
        (DerivedCategory.Q.map v ≫ cechDerivedComparison f 𝒰 L.obj) =
      DerivedCategory.Q.map (cechBaseChangeCochainMap hp L 𝒰 v) ≫
        cechDerivedComparison f' (inverseImageCover g 𝒰)
          ((Scheme.Modules.pullback g).obj L.obj) := by
  let := isAffineHom_of_isPullback_spec hp
  apply (perfectScalarDerivedTargetHomEquiv φ.hom K hK _).injective
  rw [perfectScalarDerivedTargetHomEquiv_perfectModelBaseChange,
    perfectScalarDerivedTargetHomEquiv_apply]
  simp only [cechBaseChangeCochainMap, baseChange, Functor.map_comp, Category.assoc]
  rw [← derivedComplexAdjunctionUnit_naturality_assoc]
  rw [← Functor.map_comp_assoc, ← DerivedCategory.Q.map_comp]
  have ha := cechDerivedBaseChangeMap_eq_adjunct φ f f' g hp.w L.obj 𝒰
  simp only [scalarCechDerivedBaseChangeMap] at ha
  rw [← reassoc_of% ha]
  rw [← cechDerivedComparison_baseChange]

end Pullback

end Langlands.AlgebraicGeometry.Modules.CechResolution
