/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle

/-! # The positive connecting arrow before specializing the abelian category -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u v w
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

/-- The positive connecting arrow, shifted once with its shift-addition comparison.
Source: blueprint latest, geometric classes proof, clause (2).
(blueprint: def-sfb-positive-exact-boundary).
This is the actual connecting arrow of the supplied short exact sequence,
constructed with the category witnesses still abstract. -/
def positiveExactBoundary {C : Type u} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] (s : ShortComplex C) (hs : s.ShortExact) :
    ((DerivedCategory.singleFunctor C 0).obj s.X₃)⟦(1 : ℤ)⟧ ⟶
      ((DerivedCategory.singleFunctor C 0).obj s.X₁)⟦(2 : ℤ)⟧ :=
  hs.singleδ⟦(1 : ℤ)⟧' ≫
    (shiftFunctorAdd (DerivedCategory C) (1 : ℤ) 1).inv.app
      ((DerivedCategory.singleFunctor C 0).obj s.X₁)

end AlgebraicGeometry.ProEtale.SpTowerClasses
