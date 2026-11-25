/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection

/-!
# Objectwise application of compact-support projection

This names the existing canonical transformation's component without repeatedly expanding
its bifunctor-category instance arguments at concrete module coefficients.
Source: current blueprint, `lem-pur-coprojection`, canonical-map paragraph.
-/
@[expose] public section
set_option autoImplicit false

universe u' u
open CategoryTheory MonoidalCategory AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  [UpperStarPreservesFlat A]
  {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

end AlgebraicGeometry.ProEtale
