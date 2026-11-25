/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerTraceModels
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt

/-! # Named Ext existence for diagonal coefficient sheaves

Source: Mathlib's Ext existence for Grothendieck abelian categories.
(blueprint: lem-diagonal-cyclic-coefficient-has-ext).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- Coefficient sheaves have Ext, with the standard proof shared by name.
Source: Mathlib `IsGrothendieckAbelian.hasExt`.
(blueprint: lem-diagonal-cyclic-coefficient-has-ext).
Proof: module sheaves form a Grothendieck abelian category. Apply its standard
Ext existence instance; this merely names that existing proof. -/
theorem cyclicCoefficientHasExt (l : ℕ) [Fact l.Prime] (W : Scheme.{u}) :
    HasExt.{u + 1} (DiagonalMod l W) := by
  infer_instance

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
