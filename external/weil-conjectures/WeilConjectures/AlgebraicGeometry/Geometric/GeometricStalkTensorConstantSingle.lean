/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedTensorStalk

/-! # Geometric stalks and tensoring with a constant degree-zero module

Source: Stacks Project, Tags 03PT and 07A4.
(blueprint: lem-sfb-geometric-stalk-tensor-constant-single)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Etale

/-- A geometric stalk commutes with derived tensor against a constant module in degree zero.

Source: Stacks Project, etale-cohomology.tex, proof of Tag 09BI; Tags 03PT and 07A4.
(blueprint: lem-sfb-geometric-stalk-tensor-constant-single)

Proof. Apply `exists_derivedTensor_stalk_iso` to L and the constant sheaf of N
placed in degree zero. This identifies the stalk of the derived tensor with the
tensor of the two derived stalks. The exact-functor comparison
`mapDerivedCategorySingleFunctor` identifies the second stalk with the degree-zero
complex on the ordinary stalk of the constant sheaf. The constant-stalk isomorphism
identifies that module with N. Tensor this composite on the left by the derived
stalk of L and compose with the first isomorphism. No boundedness, finiteness or
Noetherian hypothesis is used, including for zero modules and zero rings. -/
theorem geometricStalk_tensor_constant_single
    (R : Type (u + 1)) [CommRing R] {X : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (L : _root_.DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)))
    (N : ModuleCat.{u + 1} R) :
    let F := (pointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} R)
    letI : F.Additive := (pointSmallEtale x).sheafFiber_additive
    Nonempty
      (F.mapDerivedCategory.obj
          (((derivedTensor (ModuleCat.{u + 1} R) X).obj L).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj
              ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj N))) ≅
        F.mapDerivedCategory.obj L ⊗
          (_root_.DerivedCategory.singleFunctor (ModuleCat.{u + 1} R) 0).obj N)
    := by
  let F := (pointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} R)
  let : F.Additive := (pointSmallEtale x).sheafFiber_additive
  have : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} R)) :=
    CategoryTheory.Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  obtain ⟨e⟩ := ExactFunctorTensorComparison.exists_iso
    (F := F) (exactFunctor_tensor_comparison F)
  let M := (_root_.DerivedCategory.singleFunctor _ 0).obj
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj N)
  have ht : derivedTensor (ModuleCat.{u + 1} R) X =
      curriedTensor (_root_.DerivedCategory
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))) := rfl
  have h : ((derivedTensor (ModuleCat.{u + 1} R) X).obj L).obj M =
      ((curriedTensor (_root_.DerivedCategory
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)))).obj L).obj M :=
    congrArg (fun H ↦ (H.obj L).obj M) ht
  let e₀ := F.mapDerivedCategory.mapIso (eqToIso h) ≪≫ e L M
  refine ⟨e₀ ≪≫ ?_⟩
  let eN := (F.mapDerivedCategorySingleFunctor 0).app
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj N) ≪≫
    (_root_.DerivedCategory.singleFunctor (ModuleCat.{u + 1} R) 0).mapIso
      ((pointSmallEtale x).sheafFiberConstantSheafIso N)
  exact (tensorLeft (F.mapDerivedCategory.obj L)).mapIso eN

end AlgebraicGeometry.Etale
