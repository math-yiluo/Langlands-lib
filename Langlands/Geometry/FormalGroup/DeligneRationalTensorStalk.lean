import Langlands.Geometry.FormalGroup.DeligneRationalStalkBaseChange
import Mathlib.Topology.Sheaves.Sheafify

/-! # Tensor products and the actual rational stalk of a Deligne sheaf -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.DeligneFormalSpace

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped ChangeOfRings

variable {O : Type u} [CommRing O] (F : Type u) [Field F] [Algebra O F]
  (X : TopCat.{u})

/-- Scalar extension of the actual stalk identifies with the stalk of the
sectionwise extension, followed by the actual sheafification unit. -/
def rationalTensorStalkIso (M : X.Sheaf (ModuleCat.{u} O)) (x : X) :
    (ModuleCat.extendScalars (algebraMap O F)).obj
        (TopCat.Presheaf.stalk M.obj x) ≅
      TopCat.Presheaf.stalk ((rationalSheafFunctor F X).obj M).obj x := by
  let P := (rationalPresheafFunctor F X).obj M
  let j := Opens.grothendieckTopology X
  letI := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x
    (ModuleCat.{u} F) P
  exact preservesColimitIso (ModuleCat.extendScalars (algebraMap O F))
    ((OpenNhds.inclusion x).op ⋙ M.obj) ≪≫
      asIso ((TopCat.Presheaf.stalkFunctor (ModuleCat.{u} F) x).map
        (toSheafify j P))

/-- The tensor/stalk comparison is computed by extension of each actual germ. -/
theorem rationalTensorStalkIso_germ (M : X.Sheaf (ModuleCat.{u} O))
    (U : Opens X) (x : X) (hx : x ∈ U) :
    (ModuleCat.extendScalars (algebraMap O F)).map
        (TopCat.Presheaf.germ M.obj U x hx) ≫
          (rationalTensorStalkIso F X M x).hom =
      (toSheafify (Opens.grothendieckTopology X)
        ((rationalPresheafFunctor F X).obj M)).app (.op U) ≫
          TopCat.Presheaf.germ ((rationalSheafFunctor F X).obj M).obj U x hx := by
  dsimp only [rationalTensorStalkIso, Iso.trans_hom, Iso.symm_hom, asIso_hom]
  erw [← Category.assoc,
    ι_preservesColimitIso_hom (ModuleCat.extendScalars (algebraMap O F))
      ((OpenNhds.inclusion x).op ⋙ M.obj) (.op ⟨U, hx⟩)]
  exact TopCat.Presheaf.stalkFunctor_map_germ U x hx
    (toSheafify (Opens.grothendieckTopology X)
      ((rationalPresheafFunctor F X).obj M))

/-- A pure tensor with an integral germ becomes the germ of the corresponding
sectionwise pure tensor through the actual sheafification unit. -/
theorem rationalTensorStalkIso_tmul_germ (M : X.Sheaf (ModuleCat.{u} O))
    (U : Opens X) (x : X) (hx : x ∈ U) (a : F) (m : M.obj.obj (.op U)) :
    (rationalTensorStalkIso F X M x).hom
        (a ⊗ₜ[O, algebraMap O F] (TopCat.Presheaf.germ M.obj U x hx m)) =
      TopCat.Presheaf.germ ((rationalSheafFunctor F X).obj M).obj U x hx
        ((toSheafify (Opens.grothendieckTopology X)
          ((rationalPresheafFunctor F X).obj M)).app (.op U)
            (a ⊗ₜ[O, algebraMap O F] m)) :=
  congrArg (fun k => k (a ⊗ₜ[O, algebraMap O F] m))
    (rationalTensorStalkIso_germ F X M U x hx)

/-- The existing integral-to-rational stalk map is exactly the tensor unit
followed by the constructed comparison, after restricting scalars to O. -/
theorem rationalTensorStalkIso_unit (M : X.Sheaf (ModuleCat.{u} O)) (x : X) :
    (ModuleCat.extendRestrictScalarsAdj (algebraMap O F)).unit.app
        (TopCat.Presheaf.stalk M.obj x) ≫
          (ModuleCat.restrictScalars (algebraMap O F)).map
            (rationalTensorStalkIso F X M x).hom =
      integralRationalStalkMap F X M x := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hx
  have h := (ModuleCat.extendRestrictScalarsAdj (algebraMap O F)).unit.naturality
    (TopCat.Presheaf.germ M.obj U x hx)
  change TopCat.Presheaf.germ M.obj U x hx ≫
      (ModuleCat.extendRestrictScalarsAdj (algebraMap O F)).unit.app
        (TopCat.Presheaf.stalk M.obj x) =
    (ModuleCat.extendRestrictScalarsAdj (algebraMap O F)).unit.app
      (M.obj.obj (.op U)) ≫
        (ModuleCat.restrictScalars (algebraMap O F)).map
          ((ModuleCat.extendScalars (algebraMap O F)).map
            (TopCat.Presheaf.germ M.obj U x hx)) at h
  rw [← Category.assoc, h,
    Category.assoc, ← Functor.map_comp, rationalTensorStalkIso_germ,
    Functor.map_comp, integralRationalStalkMap_germ]
  rfl

/-- The comparison identifies the integral map on every element with 1 tensor m. -/
theorem rationalTensorStalkIso_one_tmul (M : X.Sheaf (ModuleCat.{u} O))
    (x : X) (m : TopCat.Presheaf.stalk (C := ModuleCat.{u} O) M.obj x) :
    (rationalTensorStalkIso F X M x).hom ((1 : F) ⊗ₜ[O, algebraMap O F] m) =
      integralRationalStalkMap F X M x m :=
  congrArg (fun k => k m) (rationalTensorStalkIso_unit F X M x)

/-- Naturality of the tensor/stalk comparison for every actual integral sheaf map. -/
theorem rationalTensorStalkIso_naturality {M N : X.Sheaf (ModuleCat.{u} O)}
    (f : M ⟶ N) (x : X) :
    (ModuleCat.extendScalars (algebraMap O F)).map
        ((TopCat.Presheaf.stalkFunctor (ModuleCat.{u} O) x).map f.hom) ≫
          (rationalTensorStalkIso F X N x).hom =
      (rationalTensorStalkIso F X M x).hom ≫
        (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} F) x).map
          ((rationalSheafFunctor F X).map f).hom := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  change (rationalTensorStalkIso F X N x).hom
      ((ModuleCat.extendScalars (algebraMap O F)).map
        ((TopCat.Presheaf.stalkFunctor (ModuleCat.{u} O) x).map f.hom)
          ((1 : F) ⊗ₜ[O, algebraMap O F] m)) =
    (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} F) x).map
      ((rationalSheafFunctor F X).map f).hom
        ((rationalTensorStalkIso F X M x).hom
          ((1 : F) ⊗ₜ[O, algebraMap O F] m))
  rw [ModuleCat.ExtendScalars.map_tmul, rationalTensorStalkIso_one_tmul,
    rationalTensorStalkIso_one_tmul]
  exact congrArg (fun k => k m) (integralRationalStalkMap_naturality F f x)

end Langlands.DeligneFormalSpace
