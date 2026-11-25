/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Roos.RoosCohomologyBoundary
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# The epimorphic projection from Roos cohomology to the inverse limit

Source: Stacks Project, Tag 07KY, the kernel extraction in the proof of the Milnor
sequence (blueprint: lem-weil-pbc-roos-cohomology-projection).
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
