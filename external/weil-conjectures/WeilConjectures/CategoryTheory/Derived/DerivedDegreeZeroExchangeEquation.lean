/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.Single
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs

/-! # The degree-zero exchange equation

This transparent proposition records the ordinary/derived exchange equation with
its four specified single-complex comparisons. It fixes the generic category
instances before specializing to categories of module sheaves.

Source: Stacks Project, Derived Categories, Tags 070K and 09T5.
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions A]
  [Abelian.HasKInjectiveResolutions C]

end CategoryTheory
