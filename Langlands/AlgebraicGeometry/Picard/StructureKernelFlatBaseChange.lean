import Langlands.AlgebraicGeometry.Picard.StructureKernelModule
import Langlands.AlgebraicGeometry.Modules.FlatPullbackExactProof
import Langlands.AlgebraicGeometry.Modules.AffinePushforwardBaseChange
import Langlands.AlgebraicGeometry.Modules.PullbackUnitProofs
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # Flat base change of the actual structure-map kernel module -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Scheme.Modules

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard.StructureKernelFlatBaseChange

open StructureKernelModule
open Langlands.AlgebraicGeometry.Modules.DerivedSections

private lemma pullbackUnitCongr {U V : Scheme.{u}} {a b : U ⟶ V} (h : a = b) :
    (Scheme.Modules.pullbackCongr h).hom.app (SheafOfModules.unit V.ringCatSheaf) ≫
        (pullbackUnitIso b).hom = (pullbackUnitIso a).hom := by
  subst h
  rfl

variable {X Y X' Y' : Scheme.{u}}
  (b : X' ⟶ X) (i : Y ⟶ X) (i' : Y' ⟶ X') (p : Y' ⟶ Y)
  (w : p ≫ i = i' ≫ b)

/-- The canonical structure-module isomorphisms commute with the actual pullback square. -/
lemma pullbackSquare_unit :
    (pullbackSquareIso b i i' p w).hom.app (SheafOfModules.unit X.ringCatSheaf) ≫
        (Scheme.Modules.pullback i').map (pullbackUnitIso b).hom ≫
        (pullbackUnitIso i').hom =
      (Scheme.Modules.pullback p).map (pullbackUnitIso i).hom ≫
        (pullbackUnitIso p).hom := by
  rw [← pullbackUnitComposition _ _ _ i' b]
  simp only [pullbackSquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [pullbackUnitCongr, pullbackUnitComposition]

/-- The actual pushforward comparison followed by the canonical structure-module map. -/
def structurePushforwardBaseChange :
    (Scheme.Modules.pullback b).obj ((Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Y.ringCatSheaf)) ⟶
      (Scheme.Modules.pushforward i').obj (SheafOfModules.unit Y'.ringCatSheaf) :=
  pushforwardBaseChange b i i' p w (SheafOfModules.unit Y.ringCatSheaf) ≫
    (Scheme.Modules.pushforward i').map (pullbackUnitIso p).hom

/-- Actual structure maps commute with base change and the canonical unit comparisons. -/
@[reassoc]
lemma structureMap_baseChange :
    (Scheme.Modules.pullback b).map (unitToPushforwardUnit i) ≫
        structurePushforwardBaseChange b i i' p w =
      (pullbackUnitIso b).hom ≫ unitToPushforwardUnit i' := by
  have hu (U V : Scheme.{u}) (a : U ⟶ V) :
      unitToPushforwardUnit a =
        (Scheme.Modules.pullbackPushforwardAdjunction a).unit.app
            (SheafOfModules.unit V.ringCatSheaf) ≫
          (Scheme.Modules.pushforward a).map (pullbackUnitIso a).hom :=
    (pullbackUnitAdjunction U V a).symm
  rw [hu _ _ i, structurePushforwardBaseChange, Functor.map_comp]
  simp only [Category.assoc]
  rw [pushforwardBaseChange_naturality_assoc]
  rw [← Functor.map_comp, ← pullbackSquare_unit b i i' p w]
  simp only [Functor.map_comp]
  rw [reassoc_of% (pullback_map_unit_comp_pushforwardBaseChange b i i' p w
    (SheafOfModules.unit X.ringCatSheaf))]
  have hn := (Scheme.Modules.pullbackPushforwardAdjunction i').unit.naturality
    (pullbackUnitIso b).hom
  simp only [Functor.id_map, Functor.comp_map] at hn
  rw [← Category.assoc, ← hn, Category.assoc]
  rw [← hu _ _ i']

variable [IsAffineHom i] (h : IsPullback p i' i b)

/-- On a cartesian square with affine vertical morphism, the actual structure pushforward
comparison is an isomorphism. -/
def structurePushforwardBaseChangeIso :
    (Scheme.Modules.pullback b).obj ((Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Y.ringCatSheaf)) ≅
      (Scheme.Modules.pushforward i').obj (SheafOfModules.unit Y'.ringCatSheaf) := by
  have : (SheafOfModules.unit Y.ringCatSheaf).IsQuasicoherent :=
    Langlands.AlgebraicGeometry.Modules.CechDegreeOne.isQuasicoherent_unit Y
  exact affinePushforwardBaseChangeIso b i i' p h _ ≪≫
    (Scheme.Modules.pushforward i').mapIso (pullbackUnitIso p)

variable [Flat b]

/-- Actual structure-map kernel modules commute with flat cartesian base change of an
 affine scheme morphism. -/
def kernelModuleFlatBaseChangeIso :
    (Scheme.Modules.pullback b).obj (kernelModule i) ≅ kernelModule i' := by
  have : PreservesFiniteLimits (Scheme.Modules.pullback b) :=
    Langlands.AlgebraicGeometry.Modules.flatPullbackExact _ _ b inferInstance
  exact (Scheme.Modules.pullback b).mapIso (kernelModuleIso i) ≪≫
    PreservesKernel.iso (Scheme.Modules.pullback b) (unitToPushforwardUnit i) ≪≫
    kernel.mapIso _ (unitToPushforwardUnit i') (pullbackUnitIso b)
      (structurePushforwardBaseChangeIso b i i' p h)
      (structureMap_baseChange b i i' p h.w) ≪≫
    (kernelModuleIso i').symm

end Langlands.AlgebraicGeometry.Picard.StructureKernelFlatBaseChange
