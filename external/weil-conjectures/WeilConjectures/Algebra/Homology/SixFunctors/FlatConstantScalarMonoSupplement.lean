/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Category.Ring.Limits

/-! # Regular constant scalars on flat module sheaves

Source: Stacks Project, Modules on Sites, Tags 03ER(3), 08FC and 03DA
(blueprint: lem-sfb-flat-constant-module-scalar-mono).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

set_option autoImplicit false

universe uC vC r m

open CategoryTheory Opposite

namespace SheafOfModules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem constantScalar_ring_injective
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    [HasSheafify J CommRingCat.{r}]
    (A : Type r) [CommRing A] (a : A)
    (ha : Function.Injective (fun x : A ↦ a * x)) (U : C) :
    Function.Injective (fun s :
        (sheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).obj (op U) ↦
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app (op U)) a * s) := by
  let B := Localization.Away a
  let f : CommRingCat.of A ⟶ CommRingCat.of B := CommRingCat.ofHom (algebraMap A B)
  have hreg : IsRegular a := (Commute.isRegular_iff (fun b ↦ mul_comm a b)).2 ha
  have hf : Function.Injective f := by
    apply (IsLocalization.injective_iff_isRegular (S := B) (Submonoid.powers a)).2
    rintro ⟨x, hx⟩
    obtain ⟨n, rfl⟩ := hx
    exact hreg.pow n
  have : Mono f := ConcreteCategory.mono_of_injective f hf
  let g := (constantSheaf J CommRingCat).map f
  have : Mono ((Functor.const Cᵒᵖ).map f) := by
    apply NatTrans.mono_of_mono_app
  have : Mono g := by
    change Mono ((presheafToSheaf J CommRingCat).map ((Functor.const Cᵒᵖ).map f))
    infer_instance
  have : Mono (g.hom.app (op U)) := inferInstance
  have hg : Function.Injective (g.hom.app (op U)) :=
    ConcreteCategory.injective_of_mono_of_preservesPullback _
  let ηA := toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))
  let ηB := toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of B))
  have hga : g.hom.app (op U) (ηA.app (op U) a) =
      ηB.app (op U) (algebraMap A B a) := by
    exact congrArg (fun k ↦ k.app (op U) a)
      (toSheafify_naturality J ((Functor.const Cᵒᵖ).map f)).symm
  have hu : IsUnit (g.hom.app (op U) (ηA.app (op U) a)) := by
    rw [hga]
    exact (IsLocalization.Away.algebraMap_isUnit (S := B) a).map (ηB.app (op U)).hom
  intro s t h
  apply hg
  apply hu.mul_right_injective
  simpa only [map_mul] using congrArg (g.hom.app (op U)) h

end SheafOfModules
