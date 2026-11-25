/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.Linear
public import WeilConjectures.CategoryTheory.ModuleObjects.RegularEnd
public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import Mathlib.CategoryTheory.Monoidal.Linear

/-! # Linearity of relative tensor products over global coefficients -/

@[expose] public noncomputable section

set_option autoImplicit false

universe v u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory

namespace CategoryTheory.Mod

/-- Relative tensor product is bilinear for any scalar action through global sections.

Source: the balanced tensor product construction, and latest blueprint
`prop-kernel-lisse.proof.md`, multiplication of character eigensections
(blueprint: lem-kernel-module-monoidal-linear).

Proof. A scalar acts through the natural transformation multiplying a module by the
corresponding global section. Its value on a tensor product equals multiplication on
the second factor, by the balancing relation. This proves linearity of left tensoring.
Naturality of the braiding transfers it to right tensoring. -/
theorem monoidalLinearOfRingHom
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    [Preadditive C] [MonoidalPreadditive C] [HasCoequalizers C]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
    {R : C} [MonObj R] [IsCommMonObj R]
    {K : Type w} [CommRing K] (φ : K →+* MonObj.Γ R) :
    let := linearOfRingHom φ
    MonoidalLinear K (Mod C R) := by
  let := linearOfRingHom φ
  have hleft (X : Mod C R) {Y Z : Mod C R} (r : K) (f : Y ⟶ Z) :
      X ◁ (r • f) = r • (X ◁ f) := by
    have h : X ◁ (r • 𝟙 Y) = r • 𝟙 (X ⊗ Y) := by
      rw [linearOfRingHom_smul_id, linearOfRingHom_smul_id,
        smulNatTrans_app_tensor]
    calc X ◁ (r • f) = X ◁ ((r • 𝟙 Y) ≫ f) := by simp
      _ = (r • 𝟙 (X ⊗ Y)) ≫ X ◁ f := by rw [whiskerLeft_comp, h]
      _ = r • (X ◁ f) := by simp
  refine ⟨hleft, ?_⟩
  intro r Y Z f X
  apply (cancel_mono (β_ Z X).hom).1
  rw [braiding_naturality_left, Linear.smul_comp, braiding_naturality_left,
    hleft, Linear.comp_smul]

/-- The unit of the relative tensor product is the regular module.
Source: the relative tensor construction
(blueprint: lem-kernel-module-monoidal-linear). -/
theorem tensorUnit_eq_regular
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    [HasCoequalizers C]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
    (R : C) [MonObj R] [IsCommMonObj R] : 𝟙_ (Mod C R) = regular R := rfl

/-- The scalar action induced through global sections acts on the regular module by
its regular endomorphism. Source: multiplication on the regular module
(blueprint: lem-kernel-module-monoidal-linear). -/
theorem regularEndRingHom_eq_smul
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    [Preadditive C] [MonoidalPreadditive C]
    {R : C} [MonObj R] [IsCommMonObj R] {K : Type w} [CommRing K]
    (φ : K →+* MonObj.Γ R) (a : K) :
    let := linearOfRingHom φ
    (regularEndRingHom (φ a)).asHom = a • 𝟙 (regular R) := by
  dsimp only
  let := linearOfRingHom φ
  rw [linearOfRingHom_smul_id]
  apply regular_hom_ext
  rw [regularEndRingHom_apply, one_comp_regularLift_regular, smulNatTrans_app_hom]
  have h := one_comp_regularLift_comp_hom (φ a).hom (𝟙 (regular R))
  rw [Mod.id_hom', Category.comp_id, one_comp_regularLift_regular] at h
  simpa only [Mod.comp_hom',
    one_comp_regularLift_regular, globalSmul, act, regular, Category.assoc,
    Category.id_comp] using h

end CategoryTheory.Mod
