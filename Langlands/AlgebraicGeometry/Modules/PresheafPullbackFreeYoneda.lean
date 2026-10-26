import Langlands.AlgebraicGeometry.Modules.PresheafPullbackTensor

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory MonoidalCategory Opposite
open AlgebraicGeometry

namespace Langlands.Scheme.Modules

variable {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)

/-- Pullback of a free Yoneda module generator is the generator at the inverse-image open. -/
def presheafPullbackFreeYonedaIso (V : Y.Opens) :
    (presheafPullback f).obj
        ((PresheafOfModules.free Y.ringCatSheaf.obj).obj (yoneda.obj V)) ≅
      (PresheafOfModules.free X.ringCatSheaf.obj).obj
        (yoneda.obj ((TopologicalSpace.Opens.map f.base).obj V)) := by
  let e := (presheafPullbackPushforwardAdjunction f).corepresentableBy
    ((PresheafOfModules.free Y.ringCatSheaf.obj).obj (yoneda.obj V))
  let e' : (presheafPushforward f ⋙ coyoneda.obj
      (op ((PresheafOfModules.free Y.ringCatSheaf.obj).obj (yoneda.obj V)))).CorepresentableBy
        ((PresheafOfModules.free X.ringCatSheaf.obj).obj
          (yoneda.obj ((TopologicalSpace.Opens.map f.base).obj V))) :=
    PresheafOfModules.pushforwardCompCoyonedaFreeYonedaCorepresentableBy
      (F := TopologicalSpace.Opens.map f.base)
      (R := X.ringCatSheaf.obj) (S := Y.ringCatSheaf.obj)
      (Functor.whiskerRight f.c (forget₂ CommRingCat.{u} RingCat.{u})) V
  exact
    { hom := e.homEquiv.symm (e'.homEquiv (𝟙 _))
      inv := e'.homEquiv.symm (e.homEquiv (𝟙 _))
      hom_inv_id := by
        apply e.homEquiv.injective
        rw [e.homEquiv_comp, Equiv.apply_symm_apply, ← e'.homEquiv_comp]
        rw [Category.id_comp]
        exact Equiv.apply_symm_apply _ _
      inv_hom_id := by
        apply e'.homEquiv.injective
        rw [e'.homEquiv_comp, Equiv.apply_symm_apply, ← e.homEquiv_comp]
        rw [Category.id_comp]
        exact Equiv.apply_symm_apply _ _ }

/-- Adjunction formula for the forward generator identification. -/
lemma presheafPullbackFreeYonedaIso_homEquiv (V : Y.Opens) :
    (presheafPullbackPushforwardAdjunction f).homEquiv _ _
      (presheafPullbackFreeYonedaIso f V).hom =
        PresheafOfModules.freeYonedaEquiv.symm
          (ModuleCat.freeMk (𝟙 ((TopologicalSpace.Opens.map f.base).obj V))) := by
  change ((presheafPullbackPushforwardAdjunction f).homEquiv _ _)
    (((presheafPullbackPushforwardAdjunction f).homEquiv _ _).symm _) = _
  rw [Equiv.apply_symm_apply]
  rfl

/-- The canonical identification sends the adjunction-unit generator to the target basis. -/
lemma presheafPullbackFreeYonedaIso_hom_unit (V : Y.Opens) :
    ((presheafPullbackPushforwardAdjunction f).homEquiv _ _
      (presheafPullbackFreeYonedaIso f V).hom).app (op V)
        (ModuleCat.freeMk (𝟙 V)) =
      ModuleCat.freeMk (𝟙 ((TopologicalSpace.Opens.map f.base).obj V)) := by
  rw [presheafPullbackFreeYonedaIso_homEquiv]
  exact PresheafOfModules.freeYonedaEquiv_symm_app _ _ _

/-- On each restricted basis, the unit followed by the identification is the inverse-image basis. -/
lemma presheafPullbackFreeYonedaIso_hom_unit_app (V U : Y.Opens) (i : U ⟶ V) :
    (presheafPullbackFreeYonedaIso f V).hom.app
        (op ((TopologicalSpace.Opens.map f.base).obj U))
      (((presheafPullbackPushforwardAdjunction f).unit.app
        ((PresheafOfModules.free Y.ringCatSheaf.obj).obj (yoneda.obj V))).app
          (op U) (ModuleCat.freeMk i)) =
        ModuleCat.freeMk ((TopologicalSpace.Opens.map f.base).map i) := by
  let m := (presheafPullbackPushforwardAdjunction f).homEquiv _ _
    (presheafPullbackFreeYonedaIso f V).hom
  have hi : ((PresheafOfModules.free Y.ringCatSheaf.obj).obj (yoneda.obj V)).map i.op
      (ModuleCat.freeMk (𝟙 V)) = ModuleCat.freeMk i := by
    dsimp only [PresheafOfModules.free, PresheafOfModules.freeObj]
    rw [ModuleCat.freeDesc_apply]
    congr 1
  have h := PresheafOfModules.naturality_apply m i.op (ModuleCat.freeMk (𝟙 V))
  rw [hi, presheafPullbackFreeYonedaIso_hom_unit] at h
  change _ = ((PresheafOfModules.free X.ringCatSheaf.obj).obj
    (yoneda.obj ((TopologicalSpace.Opens.map f.base).obj V))).map
      ((TopologicalSpace.Opens.map f.base).map i).op
        (ModuleCat.freeMk (𝟙 _)) at h
  change m.app (op U) (ModuleCat.freeMk i) = _
  rw [h]
  dsimp only [PresheafOfModules.free, PresheafOfModules.freeObj]
  rw [ModuleCat.freeDesc_apply]
  congr 1

/-- The inverse sends the distinguished basis to the adjunction-unit basis. -/
lemma presheafPullbackFreeYonedaIso_inv_basis (V : Y.Opens) :
    (presheafPullbackFreeYonedaIso f V).inv.app
        (op ((TopologicalSpace.Opens.map f.base).obj V))
      (ModuleCat.freeMk (𝟙 ((TopologicalSpace.Opens.map f.base).obj V))) =
        ((presheafPullbackPushforwardAdjunction f).unit.app
          ((PresheafOfModules.free Y.ringCatSheaf.obj).obj (yoneda.obj V))).app
            (op V) (ModuleCat.freeMk (𝟙 V)) := by
  have h := congrArg
    (fun x => (presheafPullbackFreeYonedaIso f V).inv.app
      (op ((TopologicalSpace.Opens.map f.base).obj V)) x)
    (presheafPullbackFreeYonedaIso_hom_unit f V)
  change (((presheafPullbackFreeYonedaIso f V).hom ≫
    (presheafPullbackFreeYonedaIso f V).inv).app _)
      (((presheafPullbackPushforwardAdjunction f).unit.app _).app _
        (ModuleCat.freeMk (𝟙 V))) = _ at h
  rw [Iso.hom_inv_id] at h
  exact h.symm

end Langlands.Scheme.Modules
