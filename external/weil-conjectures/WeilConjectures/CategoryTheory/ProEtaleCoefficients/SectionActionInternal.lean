/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.CategoryTheory.Ring.RingObjectSheaf
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import Mathlib.CategoryTheory.Preadditive.Basic
import WeilConjectures.CategoryTheory.Monoidal.Mod.Limits
import Mathlib.Algebra.Group.Shrink
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.CategoryTheory.SectionActionInternal

/-! # Normalized lifting of sectionwise actions

Source: blueprint main-20261015, `lem-sfb-subfield-flat.proof.md`, first two sentences;
the expanded proof of `lem-sfb-section-action-internal`.
(blueprint: lem-sfb-section-action-internal).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v w t
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct CategoryTheory.MonoidalClosed
namespace CategoryTheory


attribute [instance] Sheaf.monoidalCategory Sheaf.symmetricCategory

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  (J : GrothendieckTopology C)

/-- Sectionwise module sheaves, using existing presheaf module objects and the
full subcategory of objects whose underlying abelian presheaf is a sheaf.
Source: the category specified in lem-sfb-section-action-internal
(blueprint: lem-sfb-section-action-internal). -/
abbrev sfbSectionModules (B : Cᵒᵖ ⥤ AddCommGrpCat.{w}) [MonObj B] :=
  ObjectProperty.FullSubcategory
    (fun M : Mod (Cᵒᵖ ⥤ AddCommGrpCat.{w}) B => Presheaf.IsSheaf J M.X)

/-- The unchanged underlying abelian sheaf of a sectionwise module.
Source: lem-sfb-section-action-internal, underlying-sheaf clause
(blueprint: lem-sfb-section-action-internal). -/
def sfbSectionUnderlying {B : Cᵒᵖ ⥤ AddCommGrpCat.{w}} [MonObj B]
    (M : sfbSectionModules J B) : Sheaf J AddCommGrpCat.{w} :=
  ⟨M.obj.X, M.property⟩

/-- The coefficient abelian sheaf with its existing canonical internal ring structure.
Source: det-def-sfb-ring-object-sheaf, applied to a commutative ring sheaf
(blueprint: lem-sfb-section-action-internal). -/
abbrev sfbSectionCoefficient (B : Sheaf J CommRingCat.{w}) : Sheaf J AddCommGrpCat.{w} :=
  (sheafCompose J (forget₂ RingCat.{w} AddCommGrpCat.{w})).obj
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj B)

/-- The existing pointwise ring object on the coefficient presheaf.
Source: det-def-sfb-ring-object-sheaf and the sectionwise multiplication in the node
(blueprint: lem-sfb-section-action-internal). -/
instance sfbSectionCoefficient_presheafMonObj (B : Sheaf J CommRingCat.{w}) :
    MonObj (sfbSectionCoefficient J B).obj :=
  Functor.monObjCompForget₂
    (B.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w})

variable {B : Sheaf J CommRingCat.{w}}

private abbrev productGroup {I : Type t} [Finite I]
    (P : I → sfbSectionModules J (sfbSectionCoefficient J B).obj) (U : Cᵒᵖ) :=
  Shrink.{w} (∀ i : I, (P i).obj.X.obj U)

private def productEquiv {I : Type t} [Finite I]
    (P : I → sfbSectionModules J (sfbSectionCoefficient J B).obj) (U : Cᵒᵖ) :
    productGroup J P U ≃+ ∀ i : I, (P i).obj.X.obj U := Shrink.addEquiv

private def productPresheaf {I : Type t} [Finite I]
    (P : I → sfbSectionModules J (sfbSectionCoefficient J B).obj) :
    Cᵒᵖ ⥤ AddCommGrpCat.{w} where
  obj U := AddCommGrpCat.of (productGroup J P U)
  map {U V} f := AddCommGrpCat.ofHom
    ((productEquiv J P V).symm.toAddMonoidHom.comp
      ((AddMonoidHom.pi fun i => ((P i).obj.X.map f).hom.comp
        (Pi.evalAddMonoidHom _ i)).comp (productEquiv J P U).toAddMonoidHom))
  map_id U := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    apply (productEquiv J P U).injective
    funext i
    simp [productEquiv]
  map_comp {U V W} f g := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    apply (productEquiv J P W).injective
    funext i
    simp [productEquiv, Functor.map_comp]

private theorem productPresheaf_map {I : Type t} [Finite I]
    (P : I → sfbSectionModules J (sfbSectionCoefficient J B).obj)
    {U V : Cᵒᵖ} (f : U ⟶ V) (x : (productPresheaf J P).obj U) (i : I) :
    productEquiv J P V (((productPresheaf J P).map f).hom x) i =
      ((P i).obj.X.map f).hom (productEquiv J P U x i) := by
  exact congrFun ((productEquiv J P V).apply_symm_apply _) i

private def productProjection {I : Type t} [Finite I]
    (P : I → sfbSectionModules J (sfbSectionCoefficient J B).obj) (i : I) :
    productPresheaf J P ⟶ (P i).obj.X where
  app U := AddCommGrpCat.ofHom
    ((Pi.evalAddMonoidHom _ i).comp (productEquiv J P U).toAddMonoidHom)
  naturality U V f := by
    ext x
    exact productPresheaf_map J P f x i

private def productCone {I : Type t} [Finite I]
    (P : I → sfbSectionModules J (sfbSectionCoefficient J B).obj) :
    Fan (fun i => (P i).obj.X) :=
  Fan.mk (productPresheaf J P) (productProjection J P)

private def productConeIsLimit {I : Type t} [Finite I]
    (P : I → sfbSectionModules J (sfbSectionCoefficient J B).obj) :
    IsLimit (productCone J P) := by
  refine Fan.IsLimit.mk _ (fun s => ?_) ?_ ?_
  · exact
      { app := fun U => AddCommGrpCat.ofHom
          ((productEquiv J P U).symm.toAddMonoidHom.comp
            (AddMonoidHom.pi fun i => ((s.π.app ⟨i⟩).app U).hom))
        naturality := fun U V f => by
          apply AddCommGrpCat.hom_ext
          apply AddMonoidHom.ext
          intro x
          apply (productEquiv J P V).injective
          funext i
          simp only [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply]
          dsimp only [productCone, Fan.mk] at *
          erw [productPresheaf_map]
          change productEquiv J P V ((productEquiv J P V).symm _) i =
            ((P i).obj.X.map f).hom (productEquiv J P U ((productEquiv J P U).symm _) i)
          rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
          exact ConcreteCategory.congr_hom ((s.π.app ⟨i⟩).naturality f) x }
  · intro s i
    ext U x
    exact congrFun ((productEquiv J P U).apply_symm_apply _) i
  · intro s m hm
    ext U x
    apply (productEquiv J P U).injective
    funext i
    have h := ConcreteCategory.congr_hom (congr_app (hm i) U) x
    change productEquiv J P U ((m.app U).hom x) i = _ at h
    change productEquiv J P U ((m.app U).hom x) i =
      productEquiv J P U ((productEquiv J P U).symm _) i
    rw [AddEquiv.apply_symm_apply]
    exact h

private def productModuleCone {I : Type t} [Finite I]
    (P : I → sfbSectionModules J (sfbSectionCoefficient J B).obj) :
    Cone (Discrete.functor (fun i => (P i).obj) ⋙
      Mod.forget (sfbSectionCoefficient J B).obj) :=
  (Cone.postcompose (Discrete.compNatIsoDiscrete (fun i => (P i).obj)
    (Mod.forget (sfbSectionCoefficient J B).obj)).inv).obj (productCone J P)

private def productModuleConeIsLimit {I : Type t} [Finite I]
    (P : I → sfbSectionModules J (sfbSectionCoefficient J B).obj) :
    IsLimit (productModuleCone J P) :=
  (IsLimit.postcomposeInvEquiv (Discrete.compNatIsoDiscrete (fun i => (P i).obj)
    (Mod.forget (sfbSectionCoefficient J B).obj)) _).symm (productConeIsLimit J P)

private abbrev sectionProduct {I : Type t} [Finite I]
    (P : I → sfbSectionModules J (sfbSectionCoefficient J B).obj) :
    sfbSectionModules J (sfbSectionCoefficient J B).obj := by
  let K := Discrete.functor (fun i => (P i).obj)
  let c : Cone (K ⋙ Mod.forget (sfbSectionCoefficient J B).obj) := productModuleCone J P
  let hc : IsLimit c := productModuleConeIsLimit J P
  let m := Mod.limitModObj K hc
  refine ⟨{ X := productPresheaf J P, mod := m }, ?_⟩
  exact Sheaf.isSheaf_of_isLimit
    (Discrete.functor (fun i => sfbSectionUnderlying J (P i)))
    ((Cone.postcompose (Discrete.compNatIsoDiscrete
      (fun i => sfbSectionUnderlying J (P i)) (sheafToPresheaf J AddCommGrpCat.{w})).inv).obj
        (productCone J P))
    ((IsLimit.postcomposeInvEquiv (Discrete.compNatIsoDiscrete
      (fun i => sfbSectionUnderlying J (P i)) (sheafToPresheaf J AddCommGrpCat.{w}))
      (productCone J P)).symm (productConeIsLimit J P))

end CategoryTheory
