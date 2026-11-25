/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom

/-! # Currying for the sectionwise tensor on a general site

Source: Stacks Project, Modules on Sites, Tag 03EO. The two module universes agree,
while the site and coefficient universes remain independent.
(blueprint: lem-sf-site-tensor-hom-equiv).
-/

@[expose] public section
set_option autoImplicit false

universe a b r m
open CategoryTheory Opposite

namespace SheafOfModules.SiteTensorHom

variable {C : Type a} [Category.{b} C] {R : Cᵒᵖ ⥤ CommRingCat.{r}}

set_option hygiene false in
local notation "PMod" => PresheafOfModules.{max a b m} (R ⋙ forget₂ CommRingCat RingCat)

variable {P M N : PMod}

/-- Curry a bilinear map after restricting its first argument to each further slice.
Source: Stacks 03EO (blueprint: lem-sf-site-tensor-hom-equiv). -/
noncomputable def curryApp (φ : siteTensorPresheaf P M ⟶ N) {U : C}
    (p : P.obj (op U)) :
    (PresheafOfModules.restrictOver R U).obj M ⟶
      (PresheafOfModules.restrictOver R U).obj N where
  app W := ModuleCat.ofHom
    ((φ.app (op W.unop.left)).hom.comp
      (TensorProduct.mk (R.obj (op W.unop.left)) (P.obj (op W.unop.left))
        (M.obj (op W.unop.left)) (P.map W.unop.hom.op p)))
  naturality {W W'} f := by
    ext x
    change φ.app (op W'.unop.left)
        (P.map W'.unop.hom.op p ⊗ₜ[R.obj (op W'.unop.left)] M.map f.unop.left.op x) =
      N.map f.unop.left.op (φ.app (op W.unop.left)
        (P.map W.unop.hom.op p ⊗ₜ[R.obj (op W.unop.left)] x))
    rw [← PresheafOfModules.naturality_apply]
    change _ = φ.app (op W'.unop.left)
      (P.map f.unop.left.op (P.map W.unop.hom.op p) ⊗ₜ[R.obj (op W'.unop.left)]
        M.map f.unop.left.op x)
    congr 2
    rw [← P.map_comp_apply, ← op_comp, Over.w]

/-- Currying is linear in the first section and commutes with restriction.
Source: Stacks 03EO (blueprint: lem-sf-site-tensor-hom-equiv). -/
noncomputable def curry (φ : siteTensorPresheaf P M ⟶ N) :
    P ⟶ PresheafOfModules.homObj M N where
  app U := ModuleCat.ofHom (X := P.obj U)
    (Y := (PresheafOfModules.homObj M N).obj U)
    { toFun := curryApp φ
      map_add' p q := by
        apply PresheafOfModules.hom_ext
        intro W
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        change φ.app (op W.unop.left)
          (P.map W.unop.hom.op (p + q) ⊗ₜ[R.obj (op W.unop.left)] x) =
          φ.app (op W.unop.left) (P.map W.unop.hom.op p ⊗ₜ[R.obj (op W.unop.left)] x) +
          φ.app (op W.unop.left) (P.map W.unop.hom.op q ⊗ₜ[R.obj (op W.unop.left)] x)
        rw [map_add, TensorProduct.add_tmul, map_add]
      map_smul' s p := by
        apply PresheafOfModules.hom_ext
        intro W
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        change φ.app (op W.unop.left)
            (P.map W.unop.hom.op (s • p) ⊗ₜ[R.obj (op W.unop.left)] x) =
          (R.map W.unop.hom.op s) • φ.app (op W.unop.left)
            (P.map W.unop.hom.op p ⊗ₜ[R.obj (op W.unop.left)] x)
        rw [P.map_smul]
        change φ.app (op W.unop.left)
            ((R.map W.unop.hom.op s •
              (show P.obj (op W.unop.left) from P.map W.unop.hom.op p)) ⊗ₜ[_] x) = _
        exact LinearMap.congr_fun
          ((TensorProduct.curry (φ.app (op W.unop.left)).hom).map_smul
            (R.map W.unop.hom.op s) (P.map W.unop.hom.op p)) x }
  naturality {U V} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro p
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change φ.app (op W.unop.left)
        (P.map W.unop.hom.op (P.map f p) ⊗ₜ[R.obj (op W.unop.left)] x) =
      φ.app (op W.unop.left)
        (P.map ((Over.map f.unop).obj W.unop).hom.op p ⊗ₜ[R.obj (op W.unop.left)] x)
    rw [← P.map_comp_apply]
    rfl

/-- Evaluation on the identity slice is bilinear.
Source: Stacks 03EO (blueprint: lem-sf-site-tensor-hom-equiv). -/
noncomputable def evalId (M N : PMod) (U : C) :
    (PresheafOfModules.homObj M N).obj (op U) →ₗ[R.obj (op U)]
      M.obj (op U) →ₗ[R.obj (op U)] N.obj (op U) where
  toFun φ := (φ.app (op (Over.mk (𝟙 U)))).hom
  map_add' _ _ := rfl
  map_smul' s φ := by
    ext x
    rw [PresheafOfModules.smul_app, ModuleCat.hom_comp, LinearMap.comp_apply,
      PresheafOfModules.sectionsSMul_app_apply, PresheafOfModules.overSections_coe_apply]
    simp

/-- Uncurry by evaluating a slice homomorphism on the identity slice.
Source: Stacks 03EO (blueprint: lem-sf-site-tensor-hom-equiv). -/
noncomputable def uncurry (ψ : P ⟶ PresheafOfModules.homObj M N) :
    siteTensorPresheaf P M ⟶ N where
  app U := ModuleCat.ofHom (TensorProduct.lift
    ((evalId M N U.unop).comp (ψ.app U).hom))
  naturality {U V} f := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro p x
    change ((ψ.app V (P.map f p)).app (op (Over.mk (𝟙 V.unop)))) (M.map f x) =
      N.map f (((ψ.app U p).app (op (Over.mk (𝟙 U.unop)))) x)
    rw [PresheafOfModules.naturality_apply]
    exact (PresheafOfModules.restrictOver_hom_app_congr (ψ.app U p)
      (Category.id_comp f.unop) (M.map f x)).trans
        (PresheafOfModules.naturality_apply (ψ.app U p)
          (Over.homMk f.unop : Over.mk f.unop ⟶ Over.mk (𝟙 _)).op x)

/-- The sectionwise tensor–slice-Hom bijection.
Source: Stacks 03EO. Its inverse evaluates on the identity slice. Restriction
naturality identifies evaluation on every other slice with the restriction of
that evaluation, proving the second inverse identity. Pure tensors prove the first
(blueprint: lem-sf-site-tensor-hom-equiv). -/
noncomputable def presheafEquiv (P M N : PMod) :
    (siteTensorPresheaf P M ⟶ N) ≃ (P ⟶ PresheafOfModules.homObj M N) where
  toFun := curry
  invFun := uncurry
  left_inv φ := by
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro p x
    change φ.app U (P.map (𝟙 U) p ⊗ₜ[_] x) = φ.app U (p ⊗ₜ[_] x)
    rw [P.map_id]
    rfl
  right_inv ψ := by
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro p
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change ((ψ.app (op W.unop.left) (P.map W.unop.hom.op p)).app
      (op (Over.mk (𝟙 W.unop.left)))) x = (ψ.app U p).app W x
    rw [PresheafOfModules.naturality_apply]
    exact PresheafOfModules.restrictOver_hom_app_congr (ψ.app U p)
      (Category.id_comp W.unop.hom) x

variable {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max a b m}]
  [HasWeakSheafify J AddCommGrpCat.{max a b m}]
  {A : Sheaf J CommRingCat.{r}}

set_option hygiene false in
local notation "SMod" => SheafOfModules.{max a b m}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)

/-- Sheafification followed by sectionwise currying.
Source: Stacks 03EO. The sheafification adjunction and the presheaf currying
bijection compose; forgetting sheaf descent is fully faithful
(blueprint: lem-sf-site-tensor-hom-equiv). -/
noncomputable def equiv (P M N : SMod) :
    ((siteSheafTensorRight M).obj P ⟶ N) ≃ (P ⟶ homObj M N) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A).obj)).homEquiv
      (siteTensorPresheaf P.val M.val) N).trans
    ((presheafEquiv P.val M.val N.val).trans
      { toFun := fun f ↦ ⟨f⟩
        invFun := fun f ↦ f.val
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl })

/-- The curry formula on every further slice.
Source: Stacks 03EO. The sheafification Hom bijection precomposes with its unit,
which is exactly the definition of a local pure tensor
(blueprint: lem-sf-site-tensor-hom-equiv). -/
theorem equiv_apply (P M N : SMod) (φ : (siteSheafTensorRight M).obj P ⟶ N)
    (U : Cᵒᵖ) (p : P.val.obj U) (W : Over U.unop) (x : M.val.obj (op W.left)) :
    (((equiv P M N φ).val.app U p).app (op W)) x =
      φ.val.app (op W.left)
        (siteSheafTensorTmul P M (op W.left) (P.val.map W.hom.op p) x) := by
  rfl

/-- Currying commutes with precomposition in its first factor.
Source: Stacks 03EO. Both sides restrict the first section, apply the given
morphism, and evaluate the same bilinear map
(blueprint: lem-sf-site-tensor-hom-equiv). -/
theorem equiv_naturality {P P' M N : SMod} (f : P' ⟶ P)
    (φ : (siteSheafTensorRight M).obj P ⟶ N) :
    equiv P' M N ((siteSheafTensorRight M).map f ≫ φ) = f ≫ equiv P M N φ := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro p
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rw [equiv_apply]
  change ((siteSheafTensorRight M).map f ≫ φ).val.app _
    (siteSheafTensorTmul P' M (op W.unop.left) (P'.val.map W.unop.hom.op p) x) =
      (((equiv P M N φ).val.app U (f.val.app U p)).app W) x
  rw [equiv_apply]
  have hn := (PresheafOfModules.sheafificationAdjunction (𝟙
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A).obj)).unit.naturality
      (siteTensorHom f.val M.val)
  have ht := ConcreteCategory.congr_hom
    (congr_app (congrArg (PresheafOfModules.toPresheaf _).map hn) (op W.unop.left))
      (TensorProduct.tmul (A.obj.obj (op W.unop.left))
        (M := P'.val.obj (op W.unop.left)) (N := M.val.obj (op W.unop.left))
        (P'.val.map W.unop.hom.op p) x)
  change siteSheafTensorTmul P M (op W.unop.left)
      (f.val.app (op W.unop.left) (P'.val.map W.unop.hom.op p)) x =
    ((siteSheafTensorRight M).map f).val.app _
      (siteSheafTensorTmul P' M (op W.unop.left) (P'.val.map W.unop.hom.op p) x) at ht
  change φ.val.app _ _ = φ.val.app _ _
  exact (congrArg (φ.val.app (op W.unop.left)) ht.symm).trans
    (congrArg (fun q : P.val.obj (op W.unop.left) ↦
      φ.val.app (op W.unop.left) (siteSheafTensorTmul P M (op W.unop.left) q x))
        (PresheafOfModules.naturality_apply f.val W.unop.hom.op p))

end SheafOfModules.SiteTensorHom
