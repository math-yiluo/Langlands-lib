/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.Bifunctor
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-! # Signed evaluation for the ordinary module Hom complex

Source: Stacks Project, Tags 0A8H and 0A8X.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe w

open CategoryTheory CategoryTheory.MonoidalCategory
open CochainComplex.HomComplex
open scoped TensorProduct

namespace CochainComplex

variable {R : Type w} [CommRing R]
  (c V : CochainComplex (ModuleCat.{w} R) ℤ)

end CochainComplex
