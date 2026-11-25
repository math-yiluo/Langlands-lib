/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import Mathlib.CategoryTheory.Monoidal.Functor

/-! # Regular-module forms of monoidal unit comparisons -/

@[expose] public noncomputable section

set_option autoImplicit false

universe v₁ u₁ v₂ u₂

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CategoryTheory.Mod

variable
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [SymmetricCategory C]
    [HasCoequalizers C]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
    {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
    (R : C) [MonObj R] [IsCommMonObj R]
    {S : D} [MonObj S] [IsCommMonObj S]

/-- The regular coefficient module is the monoidal unit.
Source: the relative tensor construction (blueprint: lem-kernel-module-regular-unit). -/
def regularUnitIso : regular R ≅ 𝟙_ (Mod C R) := Iso.refl _

/-- Multiplication of the regular module is its left unitor, with both tensor factors
written as regular modules. Source: the relative tensor unit
(blueprint: lem-kernel-module-regular-unit). -/
def regularMul : regular R ⊗ regular R ⟶ regular R := (λ_ (regular R)).hom

/-- The regular multiplication is the left unitor.
Source: the relative tensor unit (blueprint: lem-kernel-module-regular-unit). -/
theorem regularMul_eq : regularMul R = (λ_ (regular R)).hom := rfl

/-- A strong monoidal functor carries the regular module to the regular module.
Source: the monoidal unit comparison (blueprint: lem-kernel-module-regular-unit). -/
def regularMapIso (F : Mod C R ⥤ Mod D S) [F.Monoidal] :
    F.obj (regular R) ≅ regular S := (Functor.Monoidal.εIso F).symm

/-- Its underlying morphism is the inverse monoidal unit comparison.
Source: the monoidal unit comparison (blueprint: lem-kernel-module-regular-unit). -/
theorem regularMapIso_hom (F : Mod C R ⥤ Mod D S) [F.Monoidal] :
    (regularMapIso R F).hom = (Functor.Monoidal.εIso F).inv := rfl

end CategoryTheory.Mod
