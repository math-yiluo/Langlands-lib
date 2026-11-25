/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.DeligneLaumon.ConstructibleTruncations
public import WeilConjectures.SmoothPurity.Finite.FiniteCoefficientPoint
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.CategoryTheory.DerivedCategory.Field.FieldDerivedScalarTower

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SmoothPurity.Sf.SfConstructibleHeart
public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients
import Mathlib.Algebra.CharP.CharAndCard

/-! # Constructible pullback comparison data

The unchanged comparison structures and scalar predicate, separated from their proofs
for compilation. Source: Bhatt--Scholze 6.8.11(3), 6.8.14(2), 6.8.15
(blueprint: def-a1-constructible-pullback-comparison-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v uC vC uB vB uD vD uA vA

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated AlgebraicGeometry

namespace WeilConjectures

-- Keep the point targets in their published small derived Hom universe when the chart API
-- imports the residue-lisse standard-size localization instance. This preference is file-local.
attribute [local instance 2000] HasDerivedCategory.ofIsGrothendieckAbelian

attribute [local irreducible] pointRationalFibre
  DerivedCategory.TStructure.t ModuleCat.extendScalars

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)

-- This cached inverse intentionally stays folded during repeated instance comparisons.

open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open GeneralAlgebraicallyClosedCoefficients (Stage inclusion stageTransition)

end WeilConjectures
