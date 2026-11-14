import Langlands.Geometry.FormalGroup.DeligneRationalTensorStalk
import Mathlib.RingTheory.Flat.Stability

/-! # Integral Deligne stalks embed in their actual rationalization -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.DeligneFormalSpace

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped ChangeOfRings

variable {O : Type u} [CommRing O] (F : Type u) [Field F] [Algebra O F]
  (X : TopCat.{u})

/-- An injective coefficient map stays injective after tensoring with a flat module. -/
theorem tensorUnit_injective_of_flat (M : ModuleCat.{u} O) [Module.Flat O M]
    (hOF : Function.Injective (algebraMap O F)) :
    Function.Injective (fun m : M =>
      ((1 : F) ⊗ₜ[O, algebraMap O F] m :
        (ModuleCat.extendScalars (algebraMap O F)).obj M)) := by
  let A := (ModuleCat.restrictScalars (algebraMap O F)).obj (ModuleCat.of F F)
  let f : O →ₗ[O] A := {
    toFun := algebraMap O F
    map_add' := map_add (algebraMap O F)
    map_smul' := fun a b => map_mul (algebraMap O F) a b }
  have h := (Module.Flat.rTensor_preserves_injective_linearMap
    (M := M) f hOF).comp (TensorProduct.lid O M).symm.injective
  simpa only [Function.comp_def, TensorProduct.lid_symm_apply,
    LinearMap.rTensor_tmul,
    show f 1 = (show A from (1 : F)) from map_one (algebraMap O F)] using h

/-- The existing integral map is injective at each flat stalk over injective coefficients. -/
theorem integralRationalStalkMap_injective (M : X.Sheaf (ModuleCat.{u} O))
    (x : X) [Module.Flat O (TopCat.Presheaf.stalk (C := ModuleCat.{u} O) M.obj x)]
    (hOF : Function.Injective (algebraMap O F)) :
    Function.Injective (integralRationalStalkMap F X M x) := by
  intro m n h
  apply tensorUnit_injective_of_flat F _ hOF
  apply (rationalTensorStalkIso F X M x).toLinearEquiv.injective
  change (rationalTensorStalkIso F X M x).hom ((1 : F) ⊗ₜ[O, algebraMap O F] m) =
    (rationalTensorStalkIso F X M x).hom ((1 : F) ⊗ₜ[O, algebraMap O F] n)
  simpa only [rationalTensorStalkIso_one_tmul] using h

variable (d : ℕ) [NeZero d] (π : O)

/-- Restricting the coefficient ring commutes with the actual lattice stalk colimit. -/
def latticeScalarStalkIso
    (M : X.Sheaf (ModuleCat.{u} (PiAlgebra d π))) (x : X) :
    TopCat.Presheaf.stalk (latticeScalarSheaf d π X M).obj x ≅
      (ModuleCat.restrictScalars (algebraMap O (PiAlgebra d π))).obj
        (TopCat.Presheaf.stalk M.obj x) :=
  (preservesColimitIso (ModuleCat.restrictScalars (algebraMap O (PiAlgebra d π)))
    ((OpenNhds.inclusion x).op ⋙ M.obj)).symm

namespace LatticePiSheaf

variable {d π X} (M : LatticePiSheaf d π X)

/-- The actual integral lattice stalk is O-flat, by flatness in the coefficient tower. -/
theorem scalarStalk_flat (x : X) :
    Module.Flat O (TopCat.Presheaf.stalk (C := ModuleCat.{u} O)
      (latticeScalarSheaf d π X M.sheaf).obj x) := by
  let N := (ModuleCat.restrictScalars (algebraMap O (PiAlgebra d π))).obj
    (TopCat.Presheaf.stalk (C := ModuleCat.{u} (PiAlgebra d π)) M.sheaf.obj x)
  have : Module.Flat (PiAlgebra d π) N := M.flat x
  have : IsScalarTower O (PiAlgebra d π) N :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Flat O N := Module.Flat.trans O (PiAlgebra d π) N
  exact Module.Flat.of_linearEquiv (latticeScalarStalkIso X d π M.sheaf x).toLinearEquiv

/-- The actual total lattice embeds into its rationalized stalk. -/
theorem integralStalk_injective (hOF : Function.Injective (algebraMap O F)) (x : X) :
    Function.Injective
      (integralRationalStalkMap F X (latticeScalarSheaf d π X M.sheaf) x) := by
  have := M.scalarStalk_flat x
  exact integralRationalStalkMap_injective F X _ x hOF

/-- Every homogeneous component embeds into the actual total rational stalk. -/
theorem componentRationalStalkMap_injective
    (hOF : Function.Injective (algebraMap O F)) (i : ZMod d) (x : X) :
    Function.Injective (M.componentRationalStalkMap F i x) := by
  have := TopCat.Presheaf.stalk_mono_of_mono (M.inclusion i) x
  exact (M.integralStalk_injective F hOF x).comp
    ((ModuleCat.mono_iff_injective _).mp
      (inferInstance : Mono ((TopCat.Presheaf.stalkFunctor (ModuleCat.{u} O) x).map
        (M.inclusion i).hom)))

end LatticePiSheaf

end Langlands.DeligneFormalSpace
