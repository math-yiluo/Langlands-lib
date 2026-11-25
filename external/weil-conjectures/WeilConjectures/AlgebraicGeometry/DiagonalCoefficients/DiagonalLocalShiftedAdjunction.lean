/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.CategoryTheory.Shift.Adjunction

/-! # Transposition of a shifted local arrow through scalar adjunctions

Source: diagonal tower coefficient changes (1), naturality of scalar transposition.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
open CategoryTheory
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- Transposing a scalar-reduced arrow cancels its source endpoint and shifts its
ordinary target transpose.
Source: diagonal tower coefficient changes (1), scalar adjunction naturality.
(blueprint: lem-diagonal-local-shifted-adjunction).
Proof: move the source endpoint and the following composite across the adjunction
using naturality of homEquiv. Cancel the endpoint isomorphism. Expand homEquiv
using the unit, move the right functor's shift comparison by naturality, and
apply compatibility of the adjunction unit with shifts. The two inverse shift
comparisons then cancel. No coefficient or Chern normalization is assumed. -/
theorem local_shifted_adjunction {C D : Type*} [Category C] [Category D]
    [HasShift C ℤ] [HasShift D ℤ]
    (F : C ⥤ D) (R : D ⥤ C) [F.CommShift ℤ] [R.CommShift ℤ]
    (a : F ⊣ R) [a.CommShift ℤ] {M T : C} {N P : D}
    (f : F.obj M ≅ N) (g : F.obj T ⟶ P) (z : M ⟶ T⟦(2 : ℤ)⟧) :
    a.homEquiv M N f.hom ≫
      R.map (f.inv ≫ F.map z ≫
        (F.commShiftIso (2 : ℤ)).hom.app T ≫ g⟦(2 : ℤ)⟧') =
      z ≫ (a.homEquiv T P g)⟦(2 : ℤ)⟧' ≫
        (R.commShiftIso (2 : ℤ)).inv.app P := by
  rw [← Adjunction.homEquiv_naturality_right]
  simp only [f.hom_inv_id_assoc]
  rw [Adjunction.homEquiv_naturality_left]
  congr 1
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [Functor.map_comp, Category.assoc]
  rw [R.commShiftIso_inv_naturality]
  rw [← a.unit_app_shift_commShiftIso_inv_app ℤ (2 : ℤ) T]
  simp only [Functor.commShiftIso_comp_inv_app, Category.assoc]
  rw [← R.map_comp_assoc, Iso.inv_hom_id_app]
  simp

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
