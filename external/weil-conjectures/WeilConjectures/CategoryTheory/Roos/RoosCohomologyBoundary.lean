/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.CategoryTheory.DerivedLimitRoosAbelianGroups
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Boundary factorization for an exact presheaf-valued realization of a Roos triangle

Source: Stacks Project, Tags 07KW and 07KY; the boundary-extraction step of
`prop-weil-pbc-roos-triangle` (blueprint: lem-weil-pbc-roos-cohomology-boundary).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe w vC uC vD uD vS uS r
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{w} C]
  [HasCountableProducts (DerivedCategory C)]
  {D : Type uD} [Category.{vD} D] {S : Type uS} [Category.{vS} S]

end CategoryTheory
