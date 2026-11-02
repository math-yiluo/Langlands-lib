import Langlands.AlgebraicGeometry.Modules.PullbackUnit
import Langlands.AlgebraicGeometry.Picard.SquareZeroUnitSheaves
import Langlands.AlgebraicGeometry.Modules.CoherentClosure
import Langlands.AlgebraicGeometry.Modules.CechDegreeOne
import Langlands.AlgebraicGeometry.Modules.SectionLocus

/-! # The actual structure-map kernel as a quasi-coherent module -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Langlands.SchemeModule
open Langlands.Scheme.Modules (unitToPushforwardUnit)

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard.StructureKernelModule

open SquareZeroUnitKernels

variable {X Y : Scheme.{u}} (i : Y ⟶ X)

local instance (U : X.Opensᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj U) ((additiveKernelPresheaf i.c).obj U) :=
  inferInstanceAs (Module (X.presheaf.obj U) (RingHom.ker (i.c.app U).hom))

/-- The actual additive structure-map kernel, with its sectionwise ideal-module action. -/
def kernelModule : X.Modules where
  val := PresheafOfModules.ofPresheaf (R := X.ringCatSheaf.obj)
    (additiveKernelPresheaf i.c) (by
      intro U V f r a
      apply Subtype.ext
      exact (X.presheaf.map f).hom.map_mul r a.val)
  isSheaf := additiveKernelPresheaf_isSheaf i.c X.sheaf.property
    (TopCat.Sheaf.pushforward_sheaf_of_sheaf i.base Y.sheaf.property)

/-- Forgetting the module action gives precisely the published actual additive kernel. -/
def kernelModuleUnderlyingIso :
    (SheafOfModules.toSheaf X.ringCatSheaf).obj (kernelModule i) ≅
      schemeAdditiveKernelSheaf i := Iso.refl _

@[simp]
lemma structureMap_app (U : X.Opens) (a : Γ(X, U)) :
    Scheme.Modules.Hom.app (unitToPushforwardUnit i) U a = i.app U a := rfl

/-- The actual ideal inclusion into the structure module. -/
def kernelModuleι : kernelModule i ⟶ structureModule X :=
  ⟨PresheafOfModules.homMk
    { app := fun U ↦ AddCommGrpCat.ofHom
        (RingHom.ker (i.c.app U).hom).subtype.toAddMonoidHom
      naturality := by intros; ext a; rfl }
    (by intros; rfl)⟩

@[simp]
lemma kernelModuleι_app (U : X.Opens) (a : Γ(kernelModule i, U)) :
    (kernelModuleι i).app U a = a.val := rfl

@[reassoc (attr := simp)]
lemma kernelModule_condition : kernelModuleι i ≫ unitToPushforwardUnit i = 0 := by
  apply Scheme.Modules.hom_ext
  intro U
  ext a
  exact a.property

/-- The sectionwise lift of a module morphism annihilated by the structure map. -/
def kernelModuleLift {M : X.Modules} (k : M ⟶ structureModule X)
    (hk : k ≫ unitToPushforwardUnit i = 0) : M ⟶ kernelModule i where
  val :=
    { app := fun U ↦ ModuleCat.ofHom
        ((k.val.app U).hom.codRestrict (RingHom.ker (i.c.app U).hom) (by
          intro a
          exact congrArg (fun q : M ⟶ (Scheme.Modules.pushforward i).obj
            (structureModule Y) ↦ q.app U.unop a) hk))
      naturality := by
        intro U V f
        ext a
        apply Subtype.ext
        exact congrArg (fun q ↦ q a) (congrArg (fun q ↦ q.hom) (k.val.naturality f)) }

@[reassoc (attr := simp)]
lemma kernelModuleLift_ι {M : X.Modules} (k : M ⟶ structureModule X)
    (hk : k ≫ unitToPushforwardUnit i = 0) : kernelModuleLift i k hk ≫ kernelModuleι i = k := by
  apply Scheme.Modules.hom_ext
  intro U
  ext a
  rfl

/-- The actual ideal module satisfies the full categorical kernel universal property. -/
def kernelModuleIsKernel : IsLimit
    (KernelFork.ofι (kernelModuleι i) (kernelModule_condition i)) :=
  KernelFork.IsLimit.ofι _ _
    (fun k hk ↦ kernelModuleLift i k hk)
    (fun k hk ↦ kernelModuleLift_ι i k hk)
    (by
      intro M k hk m hm
      apply Scheme.Modules.hom_ext
      intro U
      ext a
      apply Subtype.ext
      exact congrArg (fun q : M ⟶ structureModule X ↦ q.app U a) hm)

/-- The actual section-kernel module is the categorical kernel of the actual structure map. -/
def kernelModuleIso : kernelModule i ≅ kernel (unitToPushforwardUnit i) :=
  (kernelModuleIsKernel i).conePointUniqueUpToIso (limit.isLimit _)

/-- For an affine scheme morphism, the actual structure-map ideal module is quasi-coherent. -/
lemma kernelModule_isQuasicoherent [IsAffineHom i] : (kernelModule i).IsQuasicoherent := by
  have : (structureModule X).IsQuasicoherent :=
    Langlands.AlgebraicGeometry.Modules.CechDegreeOne.isQuasicoherent_unit X
  have : (structureModule Y).IsQuasicoherent :=
    Langlands.AlgebraicGeometry.Modules.CechDegreeOne.isQuasicoherent_unit Y
  have := Langlands.AlgebraicGeometry.Modules.QuasicoherentLocal.isQuasicoherent_pushforward
    i (structureModule Y)
  have := Langlands.AlgebraicGeometry.Modules.QuasicoherentLocal.isQuasicoherent_kernel
    (M := structureModule X) (N := (Scheme.Modules.pushforward i).obj (structureModule Y))
    (unitToPushforwardUnit i)
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (kernelModuleIso i).symm this

/-- On a locally noetherian scheme the actual structure-map ideal has finite affine sections. -/
lemma kernelModule_hasFiniteAffineSections [IsLocallyNoetherian X] :
    Langlands.AlgebraicGeometry.Modules.HasFiniteAffineSections (kernelModule i) := by
  have hO : Langlands.AlgebraicGeometry.Modules.HasFiniteAffineSections (structureModule X) := by
    intro U
    change Module.Finite Γ(X, U.1) Γ(X, U.1)
    infer_instance
  exact Langlands.AlgebraicGeometry.Modules.HasFiniteAffineSections.of_iso
    (kernelModuleIso i).symm
    (Langlands.AlgebraicGeometry.Modules.HasFiniteAffineSections.kernel (unitToPushforwardUnit i) hO)

end Langlands.AlgebraicGeometry.Picard.StructureKernelModule
