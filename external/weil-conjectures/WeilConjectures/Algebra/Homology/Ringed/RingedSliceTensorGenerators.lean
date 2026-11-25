/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
public import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Homology.SixFunctors.LocalizedSiteTensorRestrictionSupplement
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.LinearAlgebra.DirectSum.TensorProduct

/-! # Generator-normalized tensor comparison on a ringed slice site

Source: Stacks Project, Modules on Sites, Tags 0E8I, 03DI, 03EK and 0GMW
(blueprint: lem-sf-ringed-slice-tensor-generators).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r

open CategoryTheory Opposite

namespace SheafOfModules

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (A : Sheaf J CommRingCat.{max c v r}) (U : C)

open Classical in
/-- The original extension summand, followed by the actual module sheafification unit.
This is the section denoted `[x]_f`, rather than an arbitrary extension generator.
Source: Stacks 03DI (blueprint: lem-sf-ringed-slice-tensor-generators). -/
def ringedSliceExtensionSection
    (G : ringedSiteModules.{max c v r}
      (((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A).over U))
    (W : Over U) (x : G.val.obj (op W)) :
    ((localizedSystemExtension.{c, v, r} A U).obj G).val.obj (op W.left) :=
  ((PresheafOfModules.sheafificationAdjunction.{max c v r, v, max c v r, c}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A).obj)).unit.app
      ((extensionByZeroPresheaf.{max c v r}
        ((sheafCompose J
          (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A) U).obj G)).app
    (op W.left) (DirectSum.lof (A.obj.obj (op W.left)) (W.left ⟶ U)
      (fun f ↦ G.val.obj (op (Over.mk f))) W.hom x)

/-- The restriction comparison from the recorded dependency, selected with its prescribed
pure-tensor normalization. That normalization determines the comparison on all sheaf maps
by the tensor and sheafification universal properties, so this selects no arbitrary map.
Source: Stacks 03EL (blueprint: lem-sf-ringed-slice-tensor-generators). -/
def ringedSliceTensorRestriction
    [HasWeakSheafify (J.over U) AddCommGrpCat.{max c v r}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (F H : ringedSiteModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A)) :
    ((siteSheafTensorRight H).obj F).over U ≅
      (siteSheafTensorRight (A := A.over U) (H.over U)).obj (F.over U) :=
  (exists_localizedSiteTensorRestriction.{c, v, max c v r, max c v r} J A U).choose F H

private abbrev Base :=
  (sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A

private abbrev Mod := ringedSiteModules.{max c v r} (Base.{c, v, r} A)
private abbrev SliceMod := ringedSiteModules.{max c v r} ((Base.{c, v, r} A).over U)

private theorem extension_unit (G : SliceMod.{c, v, r} A U) (W : Over U) (x : G.val.obj (op W)) :
    ((localizedSystemAdjunction.{c, v, r} A U).unit.app G).val.app (op W) x =
      ringedSliceExtensionSection.{c, v, r} A U G W x := by
  exact (localizedSystemAdjunction_existsUnique.{c, v, r} A U).exists.choose_spec G (op W) x

private theorem extension_hom (G : SliceMod.{c, v, r} A U) (K : Mod.{c, v, r} A)
    (f : (localizedSystemExtension.{c, v, r} A U).obj G ⟶ K) (W : Over U)
    (x : G.val.obj (op W)) :
    (((localizedSystemAdjunction.{c, v, r} A U).homEquiv G K) f).val.app (op W) x =
      f.val.app (op W.left) (ringedSliceExtensionSection.{c, v, r} A U G W x) := by
  change f.val.app (op W.left)
    (((localizedSystemAdjunction.{c, v, r} A U).unit.app G).val.app (op W) x) = _
  rw [extension_unit.{c, v, r}]

omit [HasSheafify J AddCommGrpCat.{max c v r}] in
private theorem tensor_ext
    [HasWeakSheafify J AddCommGrpCat.{max c v r}] (F H K : Mod.{c, v, r} A)
    {f g : (siteSheafTensorRight H).obj F ⟶ K}
    (h : ∀ (W : Cᵒᵖ) (x : F.val.obj W) (a : H.val.obj W),
      f.val.app W (siteSheafTensorTmul F H W x a) =
        g.val.app W (siteSheafTensorTmul F H W x a)) : f = g := by
  apply ((PresheafOfModules.sheafificationAdjunction (R := Base.{c, v, r} A) (𝟙 _)).homEquiv
    (siteTensorPresheaf F.val H.val) K).injective
  ext W : 1
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x a
  exact h W x a

omit [HasSheafify J AddCommGrpCat.{max c v r}] in
private theorem tensor_map
    [HasWeakSheafify J AddCommGrpCat.{max c v r}] (F F' H : Mod.{c, v, r} A) (f : F ⟶ F')
    (W : Cᵒᵖ) (x : F.val.obj W) (a : H.val.obj W) :
    ((siteSheafTensorRight H).map f).val.app W (siteSheafTensorTmul F H W x a) =
      siteSheafTensorTmul F' H W (f.val.app W x) a := by
  have h := (PresheafOfModules.sheafificationAdjunction (R := Base.{c, v, r} A) (𝟙
    _)).unit.naturality
    (siteTensorHom f.val H.val)
  exact (congrArg (fun k ↦ k.app W (x ⊗ₜ[A.obj.obj W] a)) h).symm

omit [HasSheafify J AddCommGrpCat.{max c v r}] in
private theorem tensor_second
    [HasWeakSheafify J AddCommGrpCat.{max c v r}] (F H H' : Mod.{c, v, r} A) (h : H ⟶ H')
    (W : Cᵒᵖ) (x : F.val.obj W) (a : H.val.obj W) :
    (siteSheafTensorSecondMap F h).val.app W (siteSheafTensorTmul F H W x a) =
      siteSheafTensorTmul F H' W x (h.val.app W a) := by
  have hn := (PresheafOfModules.sheafificationAdjunction (R := Base.{c, v, r} A) (𝟙
    _)).unit.naturality
    (siteTensorSecondMap F.val h.val)
  exact (congrArg (fun k ↦ k.app W (x ⊗ₜ[A.obj.obj W] a)) hn).symm

omit [HasSheafify J AddCommGrpCat.{max c v r}] in
private theorem tensor_restrict
    [HasWeakSheafify J AddCommGrpCat.{max c v r}] (F H : Mod.{c, v, r} A) {V W : Cᵒᵖ} (f : V ⟶ W)
    (x : F.val.obj V) (a : H.val.obj V) :
    ((siteSheafTensorRight H).obj F).val.map f (siteSheafTensorTmul F H V x a) =
      siteSheafTensorTmul F H W (F.val.map f x) (H.val.map f a) := by
  exact (PresheafOfModules.naturality_apply
    ((PresheafOfModules.sheafificationAdjunction (R := Base.{c, v, r} A) (𝟙 _)).unit.app
      (siteTensorPresheaf F.val H.val)) f (x ⊗ₜ[A.obj.obj V] a)).symm

private theorem extension_map {G G' : SliceMod.{c, v, r} A U} (g : G ⟶ G')
    (W : Over U) (x : G.val.obj (op W)) :
    ((localizedSystemExtension.{c, v, r} A U).map g).val.app (op W.left)
        (ringedSliceExtensionSection.{c, v, r} A U G W x) =
      ringedSliceExtensionSection.{c, v, r} A U G' W (g.val.app (op W) x) := by
  have h := congrArg (fun k ↦ k.val.app (op W) x)
    ((localizedSystemAdjunction.{c, v, r} A U).unit.naturality g).symm
  change ((localizedSystemExtension.{c, v, r} A U).map g).val.app (op W.left)
    (((localizedSystemAdjunction.{c, v, r} A U).unit.app G).val.app (op W) x) =
      ((localizedSystemAdjunction.{c, v, r} A U).unit.app G').val.app (op W) (g.val.app (op W)
        x) at h
  simpa only [extension_unit.{c, v, r}] using h

private theorem extension_restrict (G : SliceMod.{c, v, r} A U) {V W : Cᵒᵖ} (f : V ⟶ W)
    (φ : V.unop ⟶ U) (x : G.val.obj (op (Over.mk φ))) :
    ((localizedSystemExtension.{c, v, r} A U).obj G).val.map f
        (ringedSliceExtensionSection.{c, v, r} A U G (Over.mk φ) x) =
      ringedSliceExtensionSection.{c, v, r} A U G (Over.mk (f.unop ≫ φ))
        (G.val.map (op (Over.homMk f.unop : Over.mk (f.unop ≫ φ) ⟶ Over.mk φ)) x) := by
  have h := PresheafOfModules.naturality_apply
    ((localizedSystemAdjunction.{c, v, r} A U).unit.app G).val
    (op (Over.homMk f.unop : Over.mk (f.unop ≫ φ) ⟶ Over.mk φ)) x
  have h := h.symm
  change ((localizedSystemExtension.{c, v, r} A U).obj G).val.map f
    (((localizedSystemAdjunction.{c, v, r} A U).unit.app G).val.app (op (Over.mk φ)) x) =
      ((localizedSystemAdjunction.{c, v, r} A U).unit.app G).val.app
        (op (Over.mk (f.unop ≫ φ)))
        (G.val.map (op (Over.homMk f.unop : Over.mk (f.unop ≫ φ) ⟶ Over.mk φ)) x) at h
  simpa only [extension_unit.{c, v, r}] using h

section Slice
variable [HasWeakSheafify (J.over U) AddCommGrpCat.{max c v r}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

private abbrev extensionTensor (G : SliceMod.{c, v, r} A U) (H : Mod.{c, v, r} A) :
  SliceMod.{c, v, r} A U :=
  (siteSheafTensorRight (A := A.over U) (H.over U)).obj G

private abbrev extensionPresheaf (G : SliceMod.{c, v, r} A U) :=
  (extensionByZeroPresheaf (Base.{c, v, r} A) U).obj G

private abbrev shAdj :=
  PresheafOfModules.sheafificationAdjunction.{max c v r, v, max c v r, c} (R := Base.{c, v, r}
    A) (𝟙 (Base.{c, v, r} A).obj)

private def tensorExtensionPresheafApp (G : SliceMod.{c, v, r} A U) (H : Mod.{c, v, r} A) (V :
  Cᵒᵖ) :
    (siteTensorPresheaf (extensionPresheaf.{c, v, r} A U G) H.val).obj V →ₗ[A.obj.obj V]
      ((localizedSystemExtension.{c, v, r} A U).obj (extensionTensor.{c, v, r} A U G
        H)).val.obj V := by
  classical
  let F := extensionTensor.{c, v, r} A U G H
  let u := (shAdj.{c, v, r} A).unit.app (extensionPresheaf.{c, v, r} A U F)
  let t := (PresheafOfModules.sheafificationAdjunction
    (R := (Base.{c, v, r} A).over U) (𝟙 _)).unit.app
      (siteTensorPresheaf (R := (A.over U).obj) G.val (H.over U).val)
  let l (φ : V.unop ⟶ U) :
      TensorProduct (A.obj.obj V) (G.val.obj (op (Over.mk φ))) (H.val.obj V) →ₗ[A.obj.obj V]
        ((localizedSystemExtension.{c, v, r} A U).obj F).val.obj V :=
    ((u.app V).hom.comp (DirectSum.lof (A.obj.obj V) _ _ φ)).comp
      (show _ →ₗ[A.obj.obj V] _ from (t.app (op (Over.mk φ))).hom)
  exact (DirectSum.toModule (A.obj.obj V) _ _ l).comp
    (TensorProduct.directSumLeft (A.obj.obj V) (A.obj.obj V)
      (fun φ : V.unop ⟶ U ↦ G.val.obj (op (Over.mk φ))) (H.val.obj V)).toLinearMap

open Classical in
private theorem tensorExtensionPresheafApp_of (G : SliceMod.{c, v, r} A U) (H : Mod.{c, v, r} A)
    (V : Cᵒᵖ) (φ : V.unop ⟶ U) (x : G.val.obj (op (Over.mk φ)))
    (a : H.val.obj V) :
    tensorExtensionPresheafApp.{c, v, r} A U G H V (DirectSum.lof (A.obj.obj V) _ _ φ x ⊗ₜ a) =
      ringedSliceExtensionSection.{c, v, r} A U (extensionTensor.{c, v, r} A U G H) (Over.mk φ)
        (siteSheafTensorTmul (A := A.over U) G (H.over U) (op (Over.mk φ)) x a) := by
  classical
  dsimp only [tensorExtensionPresheafApp, LinearMap.comp_apply]
  erw [TensorProduct.directSumLeft_tmul_lof, DirectSum.toModule_lof]
  rfl

open Classical in
private def tensorExtensionPresheaf (G : SliceMod.{c, v, r} A U) (H : Mod.{c, v, r} A) :
    siteTensorPresheaf (extensionPresheaf.{c, v, r} A U G) H.val ⟶
      ((localizedSystemExtension.{c, v, r} A U).obj (extensionTensor.{c, v, r} A U G H)).val where
  app V := ModuleCat.ofHom
    (X := (siteTensorPresheaf (extensionPresheaf.{c, v, r} A U G) H.val).obj V)
    (Y := ((localizedSystemExtension.{c, v, r} A U).obj
      (extensionTensor.{c, v, r} A U G H)).val.obj V)
    (tensorExtensionPresheafApp.{c, v, r} A U G H V)
  naturality {V W} f := by
    classical
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x a
    induction x using DirectSum.induction_on with
    | zero => simp only [map_zero, TensorProduct.zero_tmul]
    | of φ x =>
      change tensorExtensionPresheafApp.{c, v, r} A U G H W
        (extensionByZeroPresheafRestrictAdd (Base.{c, v, r} A) U G f (DirectSum.of _ φ x) ⊗ₜ
          H.val.map f a) =
        ((localizedSystemExtension.{c, v, r} A U).obj (extensionTensor.{c, v, r} A U G H)).val.map f
          (tensorExtensionPresheafApp.{c, v, r} A U G H V (DirectSum.of _ φ x ⊗ₜ a))
      have hr : extensionByZeroPresheafRestrictAdd (Base.{c, v, r} A) U G f
          (DirectSum.of _ φ x) =
          DirectSum.of _ (f.unop ≫ φ) (G.val.map (op (Over.homMk f.unop : Over.mk (f.unop ≫ φ)
            ⟶ Over.mk φ)) x) := by
        change (DirectSum.toAddMonoid _)
          (DirectSum.of (fun ψ : V.unop ⟶ U ↦ G.val.obj (op (Over.mk ψ))) φ x) = _
        rw [DirectSum.toAddMonoid_of]
        rfl
      rw [hr]
      erw [tensorExtensionPresheafApp_of.{c, v, r}, tensorExtensionPresheafApp_of.{c, v, r}]
      rw [extension_restrict.{c, v, r}]
      exact congrArg (ringedSliceExtensionSection.{c, v, r} A U
        (extensionTensor.{c, v, r} A U G H) (Over.mk (f.unop ≫ φ)))
        (tensor_restrict.{max c v, v, r} (A.over U) G (H.over U)
          (op (Over.homMk f.unop : Over.mk (f.unop ≫ φ) ⟶ Over.mk φ)) x a).symm
    | add x y hx hy =>
      simpa only [map_add, TensorProduct.add_tmul] using congrArg₂ (· + ·) hx hy

private def tensorUnitMap (G : SliceMod.{c, v, r} A U) (H : Mod.{c, v, r} A) :
    (PresheafOfModules.sheafification (R := Base.{c, v, r} A) (𝟙 _)).obj
      (siteTensorPresheaf (extensionPresheaf.{c, v, r} A U G) H.val) ⟶
      (siteSheafTensorRight H).obj ((localizedSystemExtension.{c, v, r} A U).obj G) :=
  (PresheafOfModules.sheafification (R := Base.{c, v, r} A) (𝟙 _)).map
    (siteTensorHom ((shAdj.{c, v, r} A).unit.app (extensionPresheaf.{c, v, r} A U G)) H.val)

omit [HasWeakSheafify (J.over U) AddCommGrpCat.{max c v r}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}] in
private theorem tensorUnitMap_isIso (G : SliceMod.{c, v, r} A U) (H : Mod.{c, v, r} A) :
    IsIso (tensorUnitMap.{c, v, r} A U G H) := by
  let f : extensionPresheaf.{c, v, r} A U G ⟶
      ((localizedSystemExtension.{c, v, r} A U).obj G).val :=
    (shAdj.{c, v, r} A).unit.app _
  let hi : PresheafOfModules.IsLocallyInjective J f := by
    change Presheaf.IsLocallyInjective J (toSheafify J (extensionPresheaf.{c, v, r} A U G).presheaf)
    infer_instance
  let hs : PresheafOfModules.IsLocallySurjective J f := by
    change Presheaf.IsLocallySurjective J
      (toSheafify J (extensionPresheaf.{c, v, r} A U G).presheaf)
    infer_instance
  exact @PresheafOfModules.sheafification_tensorHom_isIso.{c, v, max c v r, max c v r}
    C _ J A.obj (extensionPresheaf.{c, v, r} A U G)
    ((localizedSystemExtension.{c, v, r} A U).obj G).val H.val f hi hs
    (Base.{c, v, r} A).property _ _

attribute [local instance] tensorUnitMap_isIso

private def tensorForward (G : SliceMod.{c, v, r} A U) (H : Mod.{c, v, r} A) :
    (siteSheafTensorRight H).obj ((localizedSystemExtension.{c, v, r} A U).obj G) ⟶
      (localizedSystemExtension.{c, v, r} A U).obj (extensionTensor.{c, v, r} A U G H) :=
  inv (tensorUnitMap.{c, v, r} A U G H) ≫
    ((shAdj.{c, v, r} A).homEquiv _ _).symm (tensorExtensionPresheaf.{c, v, r} A U G H)

private theorem tensorForward_pure (G : SliceMod.{c, v, r} A U) (H : Mod.{c, v, r} A)
    (W : Over U) (x : G.val.obj (op W)) (a : H.val.obj (op W.left)) :
    (tensorForward.{c, v, r} A U G H).val.app (op W.left)
        (siteSheafTensorTmul _ H (op W.left) (ringedSliceExtensionSection.{c, v, r} A U G W x) a) =
      ringedSliceExtensionSection.{c, v, r} A U _ W
        (siteSheafTensorTmul (A := A.over U) G (H.over U) (op W) x a) := by
  classical
  have h : tensorUnitMap.{c, v, r} A U G H ≫ tensorForward.{c, v, r} A U G H =
      ((shAdj.{c, v, r} A).homEquiv _ _).symm (tensorExtensionPresheaf.{c, v, r} A U G H) := by
    simp only [tensorForward, IsIso.hom_inv_id_assoc]
  have h' := congrArg ((shAdj.{c, v, r} A).homEquiv _ _) h
  rw [Equiv.apply_symm_apply] at h'
  have hn := (shAdj.{c, v, r} A).unit.naturality
    (siteTensorHom ((shAdj.{c, v, r} A).unit.app (extensionPresheaf.{c, v, r} A U G)) H.val)
  have he := congrArg (fun k ↦ k.app (op W.left)
    (DirectSum.lof (A.obj.obj (op W.left)) _ _ W.hom x ⊗ₜ a)) h'
  have he' := congrArg (fun k ↦ k.app (op W.left)
    (DirectSum.lof (A.obj.obj (op W.left)) _ _ W.hom x ⊗ₜ a)) hn
  change (tensorForward.{c, v, r} A U G H).val.app (op W.left)
    ((tensorUnitMap.{c, v, r} A U G H).val.app (op W.left)
      (((shAdj.{c, v, r} A).unit.app _).app (op W.left) _)) = _ at he
  erw [← he'] at he
  exact he.trans (tensorExtensionPresheafApp_of.{c, v, r} A U G H (op W.left) W.hom x a)

attribute [irreducible] tensorForward

omit [HasWeakSheafify (J.over U) AddCommGrpCat.{max c v r}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}] in
private theorem extensionTensor_ext (G : SliceMod.{c, v, r} A U) (H K : Mod.{c, v, r} A)
    {f g : (siteSheafTensorRight H).obj ((localizedSystemExtension.{c, v, r} A U).obj G) ⟶ K}
    (h : ∀ (W : Over U) (x : G.val.obj (op W)) (a : H.val.obj (op W.left)),
      f.val.app (op W.left) (siteSheafTensorTmul _ H (op W.left)
        (ringedSliceExtensionSection.{c, v, r} A U G W x) a) =
      g.val.app (op W.left) (siteSheafTensorTmul _ H (op W.left)
        (ringedSliceExtensionSection.{c, v, r} A U G W x) a)) : f = g := by
  classical
  apply (cancel_epi (tensorUnitMap.{c, v, r} A U G H)).mp
  apply ((shAdj.{c, v, r} A).homEquiv _ K).injective
  ext V : 1
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x a
  have hn := (shAdj.{c, v, r} A).unit.naturality
    (siteTensorHom ((shAdj.{c, v, r} A).unit.app (extensionPresheaf.{c, v, r} A U G)) H.val)
  have he := congrArg (fun k ↦ k.app V (x ⊗ₜ[A.obj.obj V] a)) hn
  change _ = (tensorUnitMap.{c, v, r} A U G H).val.app V
    (((shAdj.{c, v, r} A).unit.app _).app V (x ⊗ₜ a)) at he
  change f.val.app V ((tensorUnitMap.{c, v, r} A U G H).val.app V _) =
    g.val.app V ((tensorUnitMap.{c, v, r} A U G H).val.app V _)
  erw [← he]
  change f.val.app V (siteSheafTensorTmul _ H V
    (((shAdj.{c, v, r} A).unit.app _).app V x) a) =
      g.val.app V (siteSheafTensorTmul _ H V
        (((shAdj.{c, v, r} A).unit.app _).app V x) a)
  clear he hn
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero, siteSheafTensorTmul, TensorProduct.zero_tmul]
  | of φ x => exact h (Over.mk φ) x a
  | add x y hx hy =>
    dsimp only [siteSheafTensorTmul] at hx hy ⊢
    simpa only [map_add, TensorProduct.add_tmul] using congrArg₂ (· + ·) hx hy

private def tensorBackward (G : SliceMod.{c, v, r} A U) (H : Mod.{c, v, r} A) :
    (localizedSystemExtension.{c, v, r} A U).obj (extensionTensor.{c, v, r} A U G H) ⟶
      (siteSheafTensorRight H).obj ((localizedSystemExtension.{c, v, r} A U).obj G) :=
  ((localizedSystemAdjunction.{c, v, r} A U).homEquiv _ _).symm
    ((siteSheafTensorRight (A := A.over U) (H.over U)).map
        ((localizedSystemAdjunction.{c, v, r} A U).unit.app G) ≫
      (ringedSliceTensorRestriction.{c, v, r} A U
        ((localizedSystemExtension.{c, v, r} A U).obj G) H).inv)

private theorem tensorBackward_pure (G : SliceMod.{c, v, r} A U) (H : Mod.{c, v, r} A) (W : Over U)
    (x : G.val.obj (op W)) (a : H.val.obj (op W.left)) :
    (tensorBackward.{c, v, r} A U G H).val.app (op W.left)
        (ringedSliceExtensionSection.{c, v, r} A U _ W
          (siteSheafTensorTmul (A := A.over U) G (H.over U) (op W) x a)) =
      siteSheafTensorTmul _ H (op W.left)
        (ringedSliceExtensionSection.{c, v, r} A U G W x) a := by
  have ht := (localizedSystemAdjunction.{c, v, r} A U).homEquiv _ _ |>.apply_symm_apply
    ((siteSheafTensorRight (A := A.over U) (H.over U)).map
      ((localizedSystemAdjunction.{c, v, r} A U).unit.app G) ≫
      (ringedSliceTensorRestriction.{c, v, r} A U
        ((localizedSystemExtension.{c, v, r} A U).obj G) H).inv)
  have hv := congrArg (fun z ↦ z.val.app (op W)
    (siteSheafTensorTmul (A := A.over U) G (H.over U) (op W) x a)) ht
  have he := extension_hom.{c, v, r} A U _ _
    (tensorBackward.{c, v, r} A U G H) W
    (siteSheafTensorTmul (A := A.over U) G (H.over U) (op W) x a)
  have hm := tensor_map.{max c v, v, r} (A.over U) G
    (((localizedSystemExtension.{c, v, r} A U).obj G).over U) (H.over U)
    ((localizedSystemAdjunction.{c, v, r} A U).unit.app G) (op W) x a
  have hu := congrArg (fun z ↦ siteSheafTensorTmul (A := A.over U)
    (((localizedSystemExtension.{c, v, r} A U).obj G).over U) (H.over U) (op W) z a)
    (extension_unit.{c, v, r} A U G W x)
  let e := ringedSliceTensorRestriction.{c, v, r} A U
    ((localizedSystemExtension.{c, v, r} A U).obj G) H
  have hp := (exists_localizedSiteTensorRestriction.{c, v, max c v r, max c v r}
    J A U).choose_spec.2 ((localizedSystemExtension.{c, v, r} A U).obj G) H W
      (ringedSliceExtensionSection.{c, v, r} A U G W x) a
  have hi := congrArg (fun z ↦ e.inv.val.app (op W) z) hp
  have hid := congrArg (fun k ↦ k.val.app (op W)
    (siteSheafTensorTmul _ H (op W.left)
      (ringedSliceExtensionSection.{c, v, r} A U G W x) a)) e.hom_inv_id
  have hf := congrArg (fun z ↦ e.inv.val.app (op W) z) (hm.trans hu)
  exact he.symm.trans (hv.trans (hf.trans (hi.symm.trans hid)))

attribute [irreducible] tensorBackward

private theorem forward_backward (G : SliceMod.{c, v, r} A U) (H : Mod.{c, v, r} A) :
    tensorForward.{c, v, r} A U G H ≫ tensorBackward.{c, v, r} A U G H = 𝟙 _ := by
  apply extensionTensor_ext.{c, v, r} A U G H
  intro W x a
  exact (congrArg (fun z ↦ (tensorBackward.{c, v, r} A U G H).val.app (op W.left) z)
    (tensorForward_pure.{c, v, r} A U G H W x a)).trans
      (tensorBackward_pure.{c, v, r} A U G H W x a)

private theorem backward_forward (G : SliceMod.{c, v, r} A U) (H : Mod.{c, v, r} A) :
    tensorBackward.{c, v, r} A U G H ≫ tensorForward.{c, v, r} A U G H = 𝟙 _ := by
  apply ((localizedSystemAdjunction.{c, v, r} A U).homEquiv _ _).injective
  apply tensor_ext.{max c v, v, r} (A.over U) G (H.over U)
    (((localizedSystemExtension.{c, v, r} A U).obj
      (extensionTensor.{c, v, r} A U G H)).over U)
  intro W x a
  obtain ⟨W⟩ := W
  calc
    _ = (tensorForward.{c, v, r} A U G H).val.app (op W.left)
        ((tensorBackward.{c, v, r} A U G H).val.app (op W.left)
          (ringedSliceExtensionSection.{c, v, r} A U _ W
            (siteSheafTensorTmul (A := A.over U) G (H.over U) (op W) x a))) :=
      extension_hom.{c, v, r} A U _ _ _ W _
    _ = (tensorForward.{c, v, r} A U G H).val.app (op W.left)
        (siteSheafTensorTmul _ H (op W.left)
          (ringedSliceExtensionSection.{c, v, r} A U G W x) a) :=
      congrArg (fun z ↦ (tensorForward.{c, v, r} A U G H).val.app (op W.left) z)
        (tensorBackward_pure.{c, v, r} A U G H W x a)
    _ = ringedSliceExtensionSection.{c, v, r} A U _ W
        (siteSheafTensorTmul (A := A.over U) G (H.over U) (op W) x a) :=
      tensorForward_pure.{c, v, r} A U G H W x a
    _ = _ := (extension_hom.{c, v, r} A U _ _ (𝟙 _) W _).symm

end Slice

/-- The tensor comparison is uniquely normalized on original extension sections, natural
in both variables, and its inverse is the prescribed adjunction transpose. The two inverse
identities are included in the `Iso` structure, as equalities of sheaf morphisms.
Source: Stacks 0E8I, refined by Tags 03DI, 03EK and 0GMW
(blueprint: lem-sf-ringed-slice-tensor-generators).

Proof:
1. The direct-sum Hom formula sends a slice map b to the presheaf map which on the
f-summand is b at (W,f). Sheafification extends it uniquely. Conversely, compose a sheaf
map with each original summand and the sheafification unit. The two formulas are inverse,
including under restrictions with coinciding composite indices. Consequently the actual
unit of localizedSystemAdjunction sends x to [x]_f, and these generators detect maps out
of the extension (the recorded extension-presheaf and sheafification dependencies).
2. On the extension presheaf paired with H, send a finite sum of x_f paired with a to
sum_f [x_f tensor a]_f. This is bilinear and respects restrictions; indices which merge
contribute additively in the same summand. Use
lem-pc-sites-module-sheafification-bilinear-extension and
lem-pc-sites-sheaf-tensor-bilinear-universal to obtain the unique map psi with the stated
formula. This uses no global representatives for arbitrary sheaf sections.
3. Tensor the actual unit at G with the identity on restricted H, then compose with the
inverse of the pure-tensor restriction comparison of
lem-sfb-localized-site-tensor-restriction. Transpose by the actual adjunction to obtain
kappa. The direct-sum Hom formula gives kappa([x tensor a]_f) = [x]_f tensor a.
4. The composite psi followed by kappa fixes every [x]_f tensor a. The bilinear-extension
and sheaf-tensor uniqueness statements imply that it is the identity. For the other
composite, take adjuncts: the maps agree with the unit at G tensor j*H on every slice pure
tensor, so the slice tensor universal property and adjunction give the other identity.
5. For g and h, both naturality composites send [x]_f tensor a to [g(x) tensor h(a)]_f.
The same generator uniqueness proves naturality. Composing with the inverse identities
also gives naturality of kappa. No flatness or constant-ring assumption enters. -/
theorem exists_ringedSliceTensorGenerators
    [HasWeakSheafify (J.over U) AddCommGrpCat.{max c v r}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}] :
    ∃ e : ∀ (G : ringedSiteModules.{max c v r}
        (((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A).over U))
        (H : ringedSiteModules.{max c v r}
          ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A)),
      (siteSheafTensorRight H).obj ((localizedSystemExtension.{c, v, r} A U).obj G) ≅
        (localizedSystemExtension.{c, v, r} A U).obj
          ((siteSheafTensorRight (A := A.over U) (H.over U)).obj G),
      (∀ (G : ringedSiteModules.{max c v r}
          (((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A).over U))
          (H : ringedSiteModules.{max c v r}
            ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A))
          (W : Over U) (x : G.val.obj (op W)) (a : H.val.obj (op W.left)),
        (e G H).hom.val.app (op W.left)
            (siteSheafTensorTmul _ H (op W.left)
              (ringedSliceExtensionSection.{c, v, r} A U G W x) a) =
          ringedSliceExtensionSection.{c, v, r} A U _ W
            (siteSheafTensorTmul (A := A.over U) G (H.over U) (op W) x a)) ∧
      (∀ (G : ringedSiteModules.{max c v r}
          (((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A).over U))
          (H : ringedSiteModules.{max c v r}
            ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A))
          (φ : (siteSheafTensorRight H).obj
              ((localizedSystemExtension.{c, v, r} A U).obj G) ⟶
            (localizedSystemExtension.{c, v, r} A U).obj
              ((siteSheafTensorRight (A := A.over U) (H.over U)).obj G)),
        (∀ (W : Over U) (x : G.val.obj (op W)) (a : H.val.obj (op W.left)),
          φ.val.app (op W.left)
              (siteSheafTensorTmul _ H (op W.left)
                (ringedSliceExtensionSection.{c, v, r} A U G W x) a) =
            ringedSliceExtensionSection.{c, v, r} A U _ W
              (siteSheafTensorTmul (A := A.over U) G (H.over U) (op W) x a)) →
          φ = (e G H).hom) ∧
      (∀ (G G' : ringedSiteModules.{max c v r}
          (((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A).over U))
          (H H' : ringedSiteModules.{max c v r}
            ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A))
          (g : G ⟶ G') (h : H ⟶ H'),
        (siteSheafTensorRight H).map ((localizedSystemExtension.{c, v, r} A U).map g) ≫
            siteSheafTensorSecondMap (A := A)
              ((localizedSystemExtension.{c, v, r} A U).obj G') h ≫ (e G' H').hom =
          (e G H).hom ≫ (localizedSystemExtension.{c, v, r} A U).map
            ((siteSheafTensorRight (A := A.over U) (H.over U)).map g ≫
              siteSheafTensorSecondMap (A := A.over U) G' (h.over U))) ∧
      (∀ (G : ringedSiteModules.{max c v r}
          (((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A).over U))
          (H : ringedSiteModules.{max c v r}
            ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A)),
        ((localizedSystemAdjunction.{c, v, r} A U).homEquiv _ _) (e G H).inv =
          (siteSheafTensorRight (A := A.over U) (H.over U)).map
              ((localizedSystemAdjunction.{c, v, r} A U).unit.app G) ≫
            (ringedSliceTensorRestriction.{c, v, r} A U
              ((localizedSystemExtension.{c, v, r} A U).obj G) H).inv) ∧
      (∀ (G : ringedSiteModules.{max c v r}
          (((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A).over U))
          (H : ringedSiteModules.{max c v r}
            ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A))
          (W : Over U) (x : G.val.obj (op W)) (a : H.val.obj (op W.left)),
        (e G H).inv.val.app (op W.left)
            (ringedSliceExtensionSection.{c, v, r} A U _ W
              (siteSheafTensorTmul (A := A.over U) G (H.over U) (op W) x a)) =
          siteSheafTensorTmul _ H (op W.left) (ringedSliceExtensionSection.{c, v, r} A U G W x) a) ∧
      (∀ (G : ringedSiteModules.{max c v r}
          (((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A).over U))
          (W : Over U) (x : G.val.obj (op W)),
        ((localizedSystemAdjunction.{c, v, r} A U).unit.app G).val.app (op W) x =
          ringedSliceExtensionSection.{c, v, r} A U G W x) := by
  let e (G : SliceMod.{c, v, r} A U) (H : Mod.{c, v, r} A) :
      (siteSheafTensorRight H).obj ((localizedSystemExtension.{c, v, r} A U).obj G) ≅
        (localizedSystemExtension.{c, v, r} A U).obj
          ((siteSheafTensorRight (A := A.over U) (H.over U)).obj G) :=
    { hom := tensorForward.{c, v, r} A U G H
      inv := tensorBackward.{c, v, r} A U G H
      hom_inv_id := forward_backward.{c, v, r} A U G H
      inv_hom_id := backward_forward.{c, v, r} A U G H }
  refine ⟨e, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact tensorForward_pure.{c, v, r} A U
  · intro G H φ hφ
    apply extensionTensor_ext.{c, v, r} A U G H
    intro W x a
    exact (hφ W x a).trans (tensorForward_pure.{c, v, r} A U G H W x a).symm
  · intro G G' H H' g h
    apply extensionTensor_ext.{c, v, r} A U G H
    intro W x a
    change (tensorForward.{c, v, r} A U G' H').val.app _
      ((siteSheafTensorSecondMap _ h).val.app _
        (((siteSheafTensorRight H).map
          ((localizedSystemExtension.{c, v, r} A U).map g)).val.app _ _)) =
      ((localizedSystemExtension.{c, v, r} A U).map _).val.app _
        ((tensorForward.{c, v, r} A U G H).val.app _ _)
    let F := (localizedSystemExtension.{c, v, r} A U).obj G
    let F' := (localizedSystemExtension.{c, v, r} A U).obj G'
    let u := (localizedSystemExtension.{c, v, r} A U).map g
    let T := extensionTensor.{c, v, r} A U G H
    let T' := extensionTensor.{c, v, r} A U G' H'
    let k : T ⟶ T' :=
      (siteSheafTensorRight (A := A.over U) (H.over U)).map g ≫
        siteSheafTensorSecondMap (A := A.over U) G' (h.over U)
    have hl₁ := congrArg (fun z ↦ (tensorForward.{c, v, r} A U G' H').val.app
      (op W.left) ((siteSheafTensorSecondMap F' h).val.app (op W.left) z))
      (tensor_map.{c, v, r} A F F' H u (op W.left)
        (ringedSliceExtensionSection.{c, v, r} A U G W x) a)
    have hl₂ := congrArg (fun z ↦ (tensorForward.{c, v, r} A U G' H').val.app
      (op W.left) z)
      (tensor_second.{c, v, r} A F' H H' h (op W.left)
        (u.val.app (op W.left) (ringedSliceExtensionSection.{c, v, r} A U G W x)) a)
    have hl₃ := congrArg (fun z ↦ (tensorForward.{c, v, r} A U G' H').val.app
      (op W.left) (siteSheafTensorTmul F' H' (op W.left) z
        (h.val.app (op W.left) a))) (extension_map.{c, v, r} A U g W x)
    have hl := hl₁.trans (hl₂.trans (hl₃.trans
      (tensorForward_pure.{c, v, r} A U G' H' W (g.val.app (op W) x)
        (h.val.app (op W.left) a))))
    have hs : k.val.app (op W)
        (siteSheafTensorTmul (A := A.over U) G (H.over U) (op W) x a) =
        siteSheafTensorTmul (A := A.over U) G' (H'.over U) (op W)
          (g.val.app (op W) x) (h.val.app (op W.left) a) :=
      (congrArg (fun z ↦ (siteSheafTensorSecondMap (A := A.over U) G'
        (h.over U)).val.app (op W) z)
        (tensor_map.{max c v, v, r} (A.over U) G G' (H.over U) g (op W) x a)).trans
          (tensor_second.{max c v, v, r} (A.over U) G' (H.over U) (H'.over U)
            (h.over U) (op W) (g.val.app (op W) x) a)
    have hr₁ := congrArg (fun z ↦ ((localizedSystemExtension.{c, v, r} A U).map k).val.app
      (op W.left) z) (tensorForward_pure.{c, v, r} A U G H W x a)
    have hr₂ := extension_map.{c, v, r} A U k W
      (siteSheafTensorTmul (A := A.over U) G (H.over U) (op W) x a)
    have hr₃ := congrArg (ringedSliceExtensionSection.{c, v, r} A U T' W) hs
    exact hl.trans (hr₁.trans (hr₂.trans hr₃)).symm
  · intro G H
    change ((localizedSystemAdjunction.{c, v, r} A U).homEquiv _ _)
      (tensorBackward.{c, v, r} A U G H) = _
    rw [tensorBackward, Equiv.apply_symm_apply]
  · exact tensorBackward_pure.{c, v, r} A U
  · exact extension_unit.{c, v, r} A U

end SheafOfModules
