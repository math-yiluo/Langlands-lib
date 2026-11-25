/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.PointRealizationStandardCohomology
import WeilConjectures.CategoryTheory.Triangulated.TStructure.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! # Exact restriction of point comparison data to full hearts

Source: BBD 1.3.3--1.3.6 (blueprint: lem-a1-point-realization-heart-exact).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe uC vC uB vB
open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated
namespace WeilConjectures

variable {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
  {B : Type uB} [Category.{vB} B] [Preadditive B] [HasZeroObject B]
  [HasShift B ℤ] [∀ n : ℤ, (shiftFunctor B n).Additive] [Pretriangulated B]
  [IsTriangulated B]
  {t : TStructure C} {s : TStructure B} {F : C ⥤ B}

end WeilConjectures
