/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData
import all WeilConjectures.CategoryTheory.Constant.ConstantScalarRestrictionTensorSupplement

/-! Ordinary tensor transport for a prescribed section/scalar realization.

Source: Stacks, Modules on Sites, Tag 03EK. -/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
namespace SheafOfModules.OpenTensorNormalization

namespace TensorOrdinary
variable {A : Type (u + 1)} [CommRing A] {X : Scheme.{u}}
  {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
  {i : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj}
  (e : FiniteRealization A X R i)

private def sections (M : FiniteModules A X) (W : X.ProEtᵒᵖ) :
    (e.equivalence.functor.obj M).val.obj W ≃+ M.obj.obj W :=
  { toFun := (e.underlying.hom.app M).hom.app W
    invFun := (e.underlying.inv.app M).hom.app W
    left_inv := fun x ↦ ConcreteCategory.congr_hom (congr_app
      (congrArg (sheafToPresheaf (ProEt.topology X) AddCommGrpCat.{u + 1}).map
        (e.underlying.hom_inv_id_app M)) W) x
    right_inv := fun x ↦ ConcreteCategory.congr_hom (congr_app
      (congrArg (sheafToPresheaf (ProEt.topology X) AddCommGrpCat.{u + 1}).map
        (e.underlying.inv_hom_id_app M)) W) x
    map_add' := map_add _ }

private theorem sections_map {M N : FiniteModules A X} (f : M ⟶ N)
    (W : X.ProEtᵒᵖ) (x : (e.equivalence.functor.obj M).val.obj W) :
    sections e N W ((e.equivalence.functor.map f).val.app W x) =
      f.hom.app W (sections e M W x) :=
  ConcreteCategory.congr_hom (congr_app
    (congrArg (sheafToPresheaf (ProEt.topology X) AddCommGrpCat.{u + 1}).map
      (e.underlying.hom.naturality f)) W) x

private theorem realized_tensor_ext (M N H : FiniteModules A X)
    (f g : e.equivalence.functor.obj (M ⊗ N) ⟶ e.equivalence.functor.obj H)
    (h : ∀ W x y, f.val.app W ((sections e (M ⊗ N) W).symm
        (finitePure M N W x y)) =
      g.val.app W ((sections e (M ⊗ N) W).symm (finitePure M N W x y))) : f = g := by
  have hh : e.equivalence.functor.preimage f = e.equivalence.functor.preimage g := by
    apply CategoryTheory.ConstantScalarRestriction.fixedTensor_ext (ProEt.topology X) A
    intro W x y
    have hf := sections_map e (e.equivalence.functor.preimage f) W
      ((sections e (M ⊗ N) W).symm (finitePure M N W x y))
    have hg := sections_map e (e.equivalence.functor.preimage g) W
      ((sections e (M ⊗ N) W).symm (finitePure M N W x y))
    rw [e.equivalence.functor.map_preimage, AddEquiv.apply_symm_apply] at hf hg
    exact hf.symm.trans ((congrArg (sections e H W) (h W x y)).trans hg)
  simpa only [Functor.map_preimage] using congrArg e.equivalence.functor.map hh

private theorem fixed_pure_map {M M' N N' : FiniteModules A X}
    (f : M ⟶ M') (g : N ⟶ N') (W : X.ProEtᵒᵖ)
    (x : M.obj.obj W) (y : N.obj.obj W) :
    (f ⊗ₘ g).hom.app W (finitePure M N W x y) =
      finitePure M' N' W (f.hom.app W x) (g.hom.app W y) := by
  exact (ConcreteCategory.congr_hom (congr_app
    (Functor.LaxMonoidal.μ_natural (sheafToPresheaf (ProEt.topology X)
      (ModuleCat.{u + 1} A)) f g) W) (x ⊗ₜ[A] y)).symm

private theorem sections_inv_map {M N : FiniteModules A X} (f : M ⟶ N)
    (W : X.ProEtᵒᵖ) (x : M.obj.obj W) :
    (e.equivalence.functor.map f).val.app W ((sections e M W).symm x) =
      (sections e N W).symm (f.hom.app W x) := by
  apply (sections e N W).injective
  rw [sections_map, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

private theorem realized_tensor_ext_any (M N : FiniteModules A X) (H : Mod R)
    (f g : e.equivalence.functor.obj (M ⊗ N) ⟶ H)
    (h : ∀ W x y, f.val.app W ((sections e (M ⊗ N) W).symm
        (finitePure M N W x y)) =
      g.val.app W ((sections e (M ⊗ N) W).symm (finitePure M N W x y))) : f = g := by
  let c := e.equivalence.counitIso.app H
  apply (cancel_mono c.inv).mp
  apply realized_tensor_ext e M N
  intro W x y
  exact congrArg (c.inv.val.app W) (h W x y)

private theorem ordinary_natural
    (c : ∀ M N : FiniteModules A X, e.equivalence.functor.obj (M ⊗ N) ≅
      e.equivalence.functor.obj M ⊗ e.equivalence.functor.obj N)
    (hp : ∀ M N W x y, (c M N).hom.val.app W
        ((sections e (M ⊗ N) W).symm (finitePure M N W x y)) =
      pure R _ _ W ((sections e M W).symm x) ((sections e N W).symm y))
    {M M' N N' : FiniteModules A X} (f : M ⟶ M') (g : N ⟶ N') :
    e.equivalence.functor.map (f ⊗ₘ g) ≫ (c M' N').hom =
      (c M N).hom ≫ (e.equivalence.functor.map f ⊗ₘ e.equivalence.functor.map g) := by
  apply realized_tensor_ext_any e M N
  intro W x y
  change (c M' N').hom.val.app W ((e.equivalence.functor.map (f ⊗ₘ g)).val.app W
      ((sections e (M ⊗ N) W).symm (finitePure M N W x y))) =
    (e.equivalence.functor.map f ⊗ₘ e.equivalence.functor.map g).val.app W
      ((c M N).hom.val.app W ((sections e (M ⊗ N) W).symm
        (finitePure M N W x y)))
  rw [sections_inv_map, fixed_pure_map, hp, hp]
  change pure R _ _ W ((sections e M' W).symm (f.hom.app W x))
      ((sections e N' W).symm (g.hom.app W y)) =
    (e.equivalence.functor.map f ⊗ₘ e.equivalence.functor.map g).val.app W
      (CochainScalarConstruction.pure R _ _ W _ _)
  erw [CochainScalarConstruction.pure_map R]
  rw [sections_inv_map, sections_inv_map]
  rfl

end TensorOrdinary

end SheafOfModules.OpenTensorNormalization
