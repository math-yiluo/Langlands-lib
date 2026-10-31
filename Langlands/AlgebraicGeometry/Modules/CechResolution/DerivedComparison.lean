import Langlands.AlgebraicGeometry.Modules.CechResolution.Comparison

/-! # Named canonical derived Čech comparison -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Cohomology Langlands.Cohomology.AcyclicResolution

namespace Langlands.AlgebraicGeometry.Modules.CechResolution

attribute [local instance] HasDerivedCategory.standard

variable {R : CommRingCat.{u}} {X : Scheme.{u}}
  (f : X ⟶ Spec R) (𝒰 : X.OrderedAffineCover) (M : X.Modules)

/-- The canonical map from sections of the sheafified Čech resolution to
actual derived sections, with extension to integer degrees made explicit. -/
def cechSectionsDerivedComparison :
    DerivedCategory.Q.obj
        ((((DerivedSections.relativeGlobalSections f).mapHomologicalComplex _).obj
          (cechComplex 𝒰 M)).extend ComplexShape.embeddingUpNat) ⟶
      (DerivedPlus.derivedComplex (DerivedSections.relativeGlobalSections f) ⋙
        DerivedCategory.Plus.ι).obj M :=
  letI := quasiIso_cechAug 𝒰 M
  DerivedCategory.Q.map
      (extendMapIso ComplexShape.embeddingUpNat
        (DerivedSections.relativeGlobalSections f) (cechComplex 𝒰 M)).inv ≫
    derivedResolutionComparison (DerivedSections.relativeGlobalSections f) (cechAug 𝒰 M)

/-- The named canonical map from alternating Čech cochains to actual
right derived relative global sections. -/
def cechDerivedComparison :
    DerivedCategory.Q.obj
        ((cechCochainComplex f 𝒰 M).extend ComplexShape.embeddingUpNat) ⟶
      (DerivedPlus.derivedComplex (DerivedSections.relativeGlobalSections f) ⋙
        DerivedCategory.Plus.ι).obj M :=
  DerivedCategory.Q.map
      ((ComplexShape.embeddingUpNat.extendFunctor _).map
        (sectionsComplexIso f 𝒰 M).inv) ≫
    cechSectionsDerivedComparison f 𝒰 M

/-- Separatedness and quasi-coherence make the canonical sections comparison
invertible, by the acyclicity of the Čech terms. -/
lemma isIso_cechSectionsDerivedComparison [IsSeparated f] [M.IsQuasicoherent] :
    IsIso (cechSectionsDerivedComparison f 𝒰 M) := by
  have := quasiIso_cechAug 𝒰 M
  have hiso := isIso_derivedResolutionComparison
    (DerivedSections.relativeGlobalSections f) (cechAug 𝒰 M)
    (fun i n => isZero_relativeCohomology_cechTerm f 𝒰 M i n)
  exact (DerivedCategory.Q.mapIso
    (extendMapIso ComplexShape.embeddingUpNat
      (DerivedSections.relativeGlobalSections f) (cechComplex 𝒰 M)).symm ≪≫
      @asIso _ _ _ _ _ hiso).isIso_hom

/-- The named alternating-cochain comparison is an isomorphism under the
usual separated, quasi-coherent hypotheses. -/
lemma isIso_cechDerivedComparison [IsSeparated f] [M.IsQuasicoherent] :
    IsIso (cechDerivedComparison f 𝒰 M) := by
  have hiso := isIso_cechSectionsDerivedComparison f 𝒰 M
  exact (DerivedCategory.Q.mapIso
    ((ComplexShape.embeddingUpNat.extendFunctor _).mapIso (sectionsComplexIso f 𝒰 M).symm) ≪≫
      @asIso _ _ _ _ _ hiso).isIso_hom

/-- The canonical derived Čech isomorphism, retaining its specified map. -/
def cechDerivedComparisonIso [IsSeparated f] [M.IsQuasicoherent] :
    DerivedCategory.Q.obj
        ((cechCochainComplex f 𝒰 M).extend ComplexShape.embeddingUpNat) ≅
      (DerivedPlus.derivedComplex (DerivedSections.relativeGlobalSections f) ⋙
        DerivedCategory.Plus.ι).obj M :=
  letI := isIso_cechDerivedComparison f 𝒰 M
  asIso (cechDerivedComparison f 𝒰 M)

@[simp]
lemma cechDerivedComparisonIso_hom [IsSeparated f] [M.IsQuasicoherent] :
    (cechDerivedComparisonIso f 𝒰 M).hom = cechDerivedComparison f 𝒰 M := rfl

end Langlands.AlgebraicGeometry.Modules.CechResolution
