import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.AlgebraicGeometry.Modules.Presheaf

/-! # Tensor products of free Yoneda module presheaves on opens

For opens `V` and `W` of a scheme, the free module presheaf on the Yoneda
presheaf of `V ⊓ W` is the sectionwise tensor product of the free module
presheaves on the Yoneda presheaves of `V` and `W`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory MonoidalCategory Opposite
open AlgebraicGeometry

namespace Langlands.Scheme.Modules

local instance freeYonedaTensorMonoidalCategory (X : AlgebraicGeometry.Scheme.{u}) :
    MonoidalCategory X.PresheafOfModules :=
  inferInstanceAs (MonoidalCategory (PresheafOfModulesOfCommRing.{u} X.presheaf))

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- Arrows `U ⟶ V ⊓ W` of opens correspond to pairs of arrows `U ⟶ V` and `U ⟶ W`. -/
def opensHomInfEquiv (U V W : X.Opens) : (U ⟶ V ⊓ W) ≃ (U ⟶ V) × (U ⟶ W) where
  toFun k := (k ≫ homOfLE inf_le_left, k ≫ homOfLE inf_le_right)
  invFun p := homOfLE (le_inf (leOfHom p.1) (leOfHom p.2))
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)

/-- The sections over `U` of the comparison: the free module on `U ⟶ V ⊓ W` is the
tensor product of the free modules on `U ⟶ V` and `U ⟶ W`. -/
def freeYonedaInfTensorIsoApp (V W : X.Opens) (U : X.Opensᵒᵖ) :
    ((PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj (V ⊓ W))).obj U ≅
      ((PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj V) ⊗
        (PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj W)).obj U :=
  (ModuleCat.free _).mapIso (opensHomInfEquiv U.unop V W).toIso ≪≫
    (ModuleCat.FreeMonoidal.μIso (X.presheaf.obj U) (U.unop ⟶ V) (U.unop ⟶ W)).symm

/-- Restriction in a free Yoneda module presheaf precomposes basis arrows. -/
lemma freeYoneda_map_freeMk (V : X.Opens) {U U' : X.Opensᵒᵖ} (f : U ⟶ U')
    (k : U.unop ⟶ V) :
    ((PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj V)).map f
        (ModuleCat.freeMk k) = ModuleCat.freeMk (f.unop ≫ k) := by
  dsimp only [PresheafOfModules.free, PresheafOfModules.freeObj]
  rw [ModuleCat.freeDesc_apply]
  rfl

/-- The sectionwise comparison sends the basis section at `k` to the tensor of the basis
sections at its two composites with the inclusions. -/
lemma freeYonedaInfTensorIsoApp_hom_freeMk (V W : X.Opens) (U : X.Opensᵒᵖ)
    (k : U.unop ⟶ V ⊓ W) :
    (freeYonedaInfTensorIsoApp V W U).hom (ModuleCat.freeMk k) =
      ModuleCat.freeMk (k ≫ homOfLE (inf_le_left : V ⊓ W ≤ V)) ⊗ₜ
        ModuleCat.freeMk (k ≫ homOfLE (inf_le_right : V ⊓ W ≤ W)) := by
  change (ModuleCat.FreeMonoidal.μIso (X.presheaf.obj U) _ _).inv
    ((ModuleCat.free _).map (opensHomInfEquiv U.unop V W).toIso.hom (ModuleCat.freeMk k)) = _
  rw [ModuleCat.free_map_apply, ModuleCat.FreeMonoidal.μIso_inv_freeMk]
  rfl

/-- The inverse sectionwise comparison sends a tensor of basis sections to the basis
section at the induced arrow into `V ⊓ W`. -/
lemma freeYonedaInfTensorIsoApp_inv_freeMk_tmul (V W : X.Opens) (U : X.Opensᵒᵖ)
    (i : U.unop ⟶ V) (j : U.unop ⟶ W) :
    (freeYonedaInfTensorIsoApp V W U).inv (ModuleCat.freeMk i ⊗ₜ ModuleCat.freeMk j) =
      ModuleCat.freeMk (homOfLE (le_inf (leOfHom i) (leOfHom j))) := by
  change (ModuleCat.free _).map (opensHomInfEquiv U.unop V W).toIso.inv
    ((ModuleCat.FreeMonoidal.μIso (X.presheaf.obj U) _ _).hom
      (ModuleCat.freeMk i ⊗ₜ ModuleCat.freeMk j)) = _
  rw [ModuleCat.FreeMonoidal.μIso_hom_freeMk_tmul_freeMk, ModuleCat.free_map_apply]
  rfl

/-- The isomorphism `A(V ⊓ W) ≅ A(V) ⊗ A(W)` of free Yoneda module presheaves. -/
def freeYonedaInfTensorIso (V W : X.Opens) :
    (PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj (V ⊓ W)) ≅
      (PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj V) ⊗
        (PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj W) :=
  PresheafOfModules.isoMk (freeYonedaInfTensorIsoApp V W) (fun U U' f => by
    refine ModuleCat.free_hom_ext (fun k => ?_)
    change (freeYonedaInfTensorIsoApp V W U').hom
        (((PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj (V ⊓ W))).map f
          (ModuleCat.freeMk k)) =
      ((PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj V) ⊗
        (PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj W)).map f
          ((freeYonedaInfTensorIsoApp V W U).hom (ModuleCat.freeMk k))
    rw [freeYoneda_map_freeMk, freeYonedaInfTensorIsoApp_hom_freeMk,
      freeYonedaInfTensorIsoApp_hom_freeMk]
    erw [PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul, freeYoneda_map_freeMk,
      freeYoneda_map_freeMk]
    rw [Category.assoc, Category.assoc])

/-- Component formula for the hom of `freeYonedaInfTensorIso` on basis sections. -/
lemma freeYonedaInfTensorIso_hom_app_freeMk (V W : X.Opens) (U : X.Opensᵒᵖ)
    (k : U.unop ⟶ V ⊓ W) :
    (freeYonedaInfTensorIso V W).hom.app U (ModuleCat.freeMk k) =
      ModuleCat.freeMk (k ≫ homOfLE (inf_le_left : V ⊓ W ≤ V)) ⊗ₜ
        ModuleCat.freeMk (k ≫ homOfLE (inf_le_right : V ⊓ W ≤ W)) :=
  freeYonedaInfTensorIsoApp_hom_freeMk V W U k

/-- The basis section at the identity of `V ⊓ W` goes to the tensor of the basis
sections at the two inclusions. -/
lemma freeYonedaInfTensorIso_hom_app_id (V W : X.Opens) :
    (freeYonedaInfTensorIso V W).hom.app (op (V ⊓ W)) (ModuleCat.freeMk (𝟙 (V ⊓ W))) =
      ModuleCat.freeMk (homOfLE (inf_le_left : V ⊓ W ≤ V)) ⊗ₜ
        ModuleCat.freeMk (homOfLE (inf_le_right : V ⊓ W ≤ W)) := by
  rw [freeYonedaInfTensorIso_hom_app_freeMk]
  rfl

/-- Component formula for the inverse of `freeYonedaInfTensorIso` on tensors of basis
sections. -/
lemma freeYonedaInfTensorIso_inv_app_freeMk_tmul (V W : X.Opens) (U : X.Opensᵒᵖ)
    (i : U.unop ⟶ V) (j : U.unop ⟶ W) :
    (freeYonedaInfTensorIso V W).inv.app U (ModuleCat.freeMk i ⊗ₜ ModuleCat.freeMk j) =
      ModuleCat.freeMk (homOfLE (le_inf (leOfHom i) (leOfHom j))) :=
  freeYonedaInfTensorIsoApp_inv_freeMk_tmul V W U i j

/-- `freeYonedaEquiv` evaluates a map at the basis section of the identity. -/
lemma freeYonedaEquiv_eq_app_freeMk_id {M : X.PresheafOfModules} (V : X.Opens)
    (m : (PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj V) ⟶ M) :
    PresheafOfModules.freeYonedaEquiv m = m.app (op V) (ModuleCat.freeMk (𝟙 V)) := by
  have h := PresheafOfModules.freeYonedaEquiv_symm_app M V
    (PresheafOfModules.freeYonedaEquiv m)
  rw [Equiv.symm_apply_apply] at h
  exact h.symm

/-- Maps out of `A(V) ⊗ A(W)` agree if they agree on the tensor of the basis sections at
the inclusions of `V ⊓ W` into `V` and `W`. -/
lemma freeYonedaTensor_hom_ext (V W : X.Opens) {M : X.PresheafOfModules}
    {f g : (PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj V) ⊗
        (PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj W) ⟶ M}
    (h : f.app (op (V ⊓ W)) (ModuleCat.freeMk (homOfLE (inf_le_left : V ⊓ W ≤ V)) ⊗ₜ
          ModuleCat.freeMk (homOfLE (inf_le_right : V ⊓ W ≤ W))) =
        g.app (op (V ⊓ W)) (ModuleCat.freeMk (homOfLE (inf_le_left : V ⊓ W ≤ V)) ⊗ₜ
          ModuleCat.freeMk (homOfLE (inf_le_right : V ⊓ W ≤ W)))) :
    f = g := by
  rw [← cancel_epi (freeYonedaInfTensorIso V W).hom]
  apply PresheafOfModules.freeYonedaEquiv.injective
  rw [PresheafOfModules.freeYonedaEquiv_comp, PresheafOfModules.freeYonedaEquiv_comp,
    freeYonedaEquiv_eq_app_freeMk_id, freeYonedaInfTensorIso_hom_app_id]
  exact h

end Langlands.Scheme.Modules
