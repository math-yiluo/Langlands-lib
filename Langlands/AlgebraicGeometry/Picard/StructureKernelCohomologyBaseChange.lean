import Langlands.AlgebraicGeometry.Picard.StructureKernelFlatBaseChange
import Langlands.AlgebraicGeometry.Modules.CechResolution.QuasicoherentBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Cohomology base change of actual structure-map kernels -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Scheme.Modules
open scoped TensorProduct ChangeOfRings

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard.StructureKernelCohomologyBaseChange

open StructureKernelModule StructureKernelFlatBaseChange
open Langlands.AlgebraicGeometry.Modules
open Langlands.AlgebraicGeometry.Modules.DerivedSections
open Langlands.AlgebraicGeometry.Modules.CechResolution

variable {X Y : Scheme.{u}} (i : Y ⟶ X)

/-- The categorical-kernel identification preserves the actual ideal inclusion. -/
@[reassoc (attr := simp)]
lemma kernelModuleIso_hom_ι :
    (kernelModuleIso i).hom ≫ kernel.ι (unitToPushforwardUnit i) = kernelModuleι i := by
  exact IsLimit.conePointUniqueUpToIso_hom_comp (kernelModuleIsKernel i)
    (limit.isLimit _) WalkingParallelPair.zero

/-- The inverse categorical-kernel identification preserves the actual inclusion. -/
@[reassoc (attr := simp)]
lemma kernelModuleIso_inv_ι :
    (kernelModuleIso i).inv ≫ kernelModuleι i = kernel.ι (unitToPushforwardUnit i) := by
  exact IsLimit.conePointUniqueUpToIso_inv_comp (kernelModuleIsKernel i)
    (limit.isLimit _) WalkingParallelPair.zero

section Inclusion

variable {X' Y' : Scheme.{u}}
  (b : X' ⟶ X) (i' : Y' ⟶ X') (p : Y' ⟶ Y)
  [IsAffineHom i] [Flat b] (h : IsPullback p i' i b)

/-- The actual flat kernel comparison commutes with inclusion into the structure module. -/
@[reassoc]
lemma kernelModuleFlatBaseChangeIso_ι :
    (kernelModuleFlatBaseChangeIso b i i' p h).hom ≫ kernelModuleι i' =
      (Scheme.Modules.pullback b).map (kernelModuleι i) ≫ (pullbackUnitIso b).hom := by
  have : PreservesFiniteLimits (Scheme.Modules.pullback b) :=
    Langlands.AlgebraicGeometry.Modules.flatPullbackExact _ _ b inferInstance
  simp only [kernelModuleFlatBaseChangeIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Category.assoc, kernelModuleIso_inv_ι,
    kernel.mapIso_hom, kernel.map, kernel.lift_ι, PreservesKernel.iso_hom,
    kernelComparison_comp_ι_assoc]
  rw [← Functor.map_comp_assoc, kernelModuleIso_hom_ι]

end Inclusion

section Scalar

variable {X' Y' : Scheme.{u}} {R S : CommRingCat.{u}}
  (b : X' ⟶ X) (i' : Y' ⟶ X') (p : Y' ⟶ Y)
  (φ : R ⟶ S) (f : X ⟶ Spec R) (f' : X' ⟶ Spec S)
  (hb : IsPullback b f' f (Spec.map φ)) (hφ : φ.hom.Flat)

include hb in
/-- Pullback of a morphism between affine bases is affine. -/
lemma baseChange_isAffine : IsAffineHom b :=
  MorphismProperty.of_isPullback (P := @IsAffineHom) hb.flip inferInstance

include hb hφ in
/-- Flatness of the scalar map supplies flatness of the scheme base change. -/
lemma baseChange_flat : Flat b := by
  have : Flat (Spec.map φ) := Flat.SpecMap_iff.mpr hφ
  exact MorphismProperty.of_isPullback hb.flip inferInstance

variable [IsAffineHom i] [IsSeparated f] [CompactSpace X]
  (hi : IsPullback p i' i b)

/-- Scalar flat base change of cohomology of the actual structure-map kernel. -/
def kernelModuleCohomologyFlatBaseChangeIso (n : ℕ) :
    (ModuleCat.extendScalars φ.hom).obj
        ((relativeCohomology f n).obj (kernelModule i)) ≅
      (relativeCohomology f' n).obj (kernelModule i') := by
  have : IsAffineHom b := baseChange_isAffine b φ f f' hb
  have : Flat b := baseChange_flat b φ f f' hb hφ
  have : (kernelModule i).IsQuasicoherent := kernelModule_isQuasicoherent i
  exact quasicoherentScalarBaseChangeIso b φ f f' hb.w (kernelModule i) hb hφ n ≪≫
    (relativeCohomology f' n).mapIso (kernelModuleFlatBaseChangeIso b i i' p hi)

/-- The forward map is canonical scalar base change followed by the actual kernel comparison. -/
lemma kernelModuleCohomologyFlatBaseChangeIso_hom (n : ℕ) :
    letI : IsAffineHom b := baseChange_isAffine b φ f f' hb
    letI : Flat b := baseChange_flat b φ f f' hb hφ
    letI : (kernelModule i).IsQuasicoherent := kernelModule_isQuasicoherent i
    (kernelModuleCohomologyFlatBaseChangeIso i b i' p φ f f' hb hφ hi n).hom =
      scalarBaseChangeMap φ f f' b hb.w (kernelModule i)
          (isZero_higherDirectImage_pullback_quasicoherent b (kernelModule i)) n ≫
        (relativeCohomology f' n).map (kernelModuleFlatBaseChangeIso b i i' p hi).hom := rfl

/-- On `1 ⊗ x`, the comparison is the actual semilinear map followed by the kernel map. -/
lemma kernelModuleCohomologyFlatBaseChangeIso_one_tmul
    (n : ℕ) (x : (relativeCohomology f n).obj (kernelModule i)) :
    letI : IsAffineHom b := baseChange_isAffine b φ f f' hb
    letI : Flat b := baseChange_flat b φ f f' hb hφ
    letI : (kernelModule i).IsQuasicoherent := kernelModule_isQuasicoherent i
    (kernelModuleCohomologyFlatBaseChangeIso i b i' p φ f f' hb hφ hi n).hom
        ((1 : S) ⊗ₜ[R,φ.hom] x) =
      (relativeCohomology f' n).map (kernelModuleFlatBaseChangeIso b i i' p hi).hom
        (baseChangeMap φ f f' b hb.w (kernelModule i)
          (isZero_higherDirectImage_pullback_quasicoherent b (kernelModule i))
          (fun J hJ q => (pushforwardInjectiveAcyclic X' X b J hJ q).2 R f) n x) := by
  dsimp only
  rw [kernelModuleCohomologyFlatBaseChangeIso_hom, ModuleCat.comp_apply,
    scalarBaseChangeMap_one_tmul]

/-- The same canonical cohomology comparison for the actual structure modules. -/
def structureModuleCohomologyFlatBaseChangeIso (n : ℕ) :
    (ModuleCat.extendScalars φ.hom).obj
        ((relativeCohomology f n).obj (SheafOfModules.unit X.ringCatSheaf)) ≅
      (relativeCohomology f' n).obj (SheafOfModules.unit X'.ringCatSheaf) := by
  have : IsAffineHom b := baseChange_isAffine b φ f f' hb
  have : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
    CechDegreeOne.isQuasicoherent_unit X
  exact quasicoherentScalarBaseChangeIso b φ f f' hb.w
      (SheafOfModules.unit X.ringCatSheaf) hb hφ n ≪≫
    (relativeCohomology f' n).mapIso (pullbackUnitIso b)

/-- Scalar cohomology base change commutes with the actual ideal inclusions. -/
@[reassoc]
lemma kernelModuleCohomologyFlatBaseChangeIso_ι (n : ℕ) :
    (ModuleCat.extendScalars φ.hom).map
          ((relativeCohomology f n).map (kernelModuleι i)) ≫
        (structureModuleCohomologyFlatBaseChangeIso b φ f f' hb hφ n).hom =
      (kernelModuleCohomologyFlatBaseChangeIso i b i' p φ f f' hb hφ hi n).hom ≫
        (relativeCohomology f' n).map (kernelModuleι i') := by
  have : IsAffineHom b := baseChange_isAffine b φ f f' hb
  have : Flat b := baseChange_flat b φ f f' hb hφ
  have : (kernelModule i).IsQuasicoherent := kernelModule_isQuasicoherent i
  have : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
    CechDegreeOne.isQuasicoherent_unit X
  simp only [kernelModuleCohomologyFlatBaseChangeIso,
    structureModuleCohomologyFlatBaseChangeIso, Iso.trans_hom,
    Functor.mapIso_hom, Category.assoc]
  rw [quasicoherentScalarBaseChangeIso_naturality_assoc b φ f f' hb.w hb hφ
    (M := kernelModule i) (N := SheafOfModules.unit X.ringCatSheaf)
    (kernelModuleι i) n]
  simp only [← Functor.map_comp, kernelModuleFlatBaseChangeIso_ι]

/-- The comparison on global-ring module cohomology, with the canonical scalar restrictions. -/
def kernelModuleCohomologyRestrictScalarsBaseChangeIso (n : ℕ) :
    (ModuleCat.extendScalars φ.hom).obj
        ((ModuleCat.restrictScalars (structureRingHom f).hom).obj
          ((cohomology X n).obj (kernelModule i))) ≅
      (ModuleCat.restrictScalars (structureRingHom f').hom).obj
        ((cohomology X' n).obj (kernelModule i')) :=
  (ModuleCat.extendScalars φ.hom).mapIso
      ((relativeCohomologyRestrictScalarsIso f n).app (kernelModule i)) ≪≫
    kernelModuleCohomologyFlatBaseChangeIso i b i' p φ f f' hb hφ hi n ≪≫
    ((relativeCohomologyRestrictScalarsIso f' n).app (kernelModule i')).symm

end Scalar

end Langlands.AlgebraicGeometry.Picard.StructureKernelCohomologyBaseChange
