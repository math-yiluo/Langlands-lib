/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.ConstructiblePullbackComparisonData
public import WeilConjectures.DeligneLaumon.ConstructiblePointComparisonData
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
import WeilConjectures.DeligneLaumon.PointRealizationHeartExact
import WeilConjectures.DeligneLaumon.PointRealizationStandardCohomology
import WeilConjectures.DeligneLaumon.PointScalarBetaNormalization
import WeilConjectures.DeligneLaumon.PointFiniteScalarCohomology
import WeilConjectures.DeligneLaumon.PointCommonScalarCohomology

/-! # T-exact constructible pullback and geometric-point fibres

Source: Bhatt--Scholze, Definition 6.8.10, Proposition 6.8.11(3),
Proposition 6.8.14(2) and Remark 6.8.15
(blueprint: lem-a1-constructible-pullback-t-exact).

The comparison data below package the clauses of this node. Their cohomology maps
are explicitly the composites of the truncation comparisons and the shift comparison.
The scalar square is an equality of those maps, rather than an existence of unrelated
isomorphisms. The categories and the standard pairs are the recorded intrinsic ones.

## Main statements

- `constructible_pullback_t_exact`: t-exact pullback, exact hearts and canonical cohomology.
- `constructible_pullback_scalar_compatibility`: finite and common-stage scalar squares.
- `constructible_pullback_point_fibre`: the point cohomology and degree-zero clauses.
- `constructible_point_scalar_compatibility`: the point-evaluation scalar squares.
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

section Composite

variable {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {B : Type uB} [Category.{vB} B] [Preadditive B] [HasZeroObject B]
  [HasShift B ℤ] [∀ n : ℤ, (shiftFunctor B n).Additive] [Pretriangulated B]
  {A : Type uA} [Category.{vA} A] [Preadditive A] [HasZeroObject A]
  [HasShift A ℤ] [∀ n : ℤ, (shiftFunctor A n).Additive] [Pretriangulated A]
  {t : TStructure C} {s : TStructure B} {r : TStructure A}
  {P : ObjectProperty C} {Q : ObjectProperty B} {U : ObjectProperty A}
  {F : C ⥤ B} {G : B ⥤ A}

end Composite

section PointComparison

variable {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
  {B : Type uB} [Category.{vB} B] [Preadditive B] [HasZeroObject B]
  [HasShift B ℤ] [∀ n : ℤ, (shiftFunctor B n).Additive] [Pretriangulated B]
  [IsTriangulated B]
  {t : TStructure C} {s : TStructure B} {F : C ⥤ B}

end PointComparison

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open GeneralAlgebraicallyClosedCoefficients (Stage inclusion stageTransition)

end WeilConjectures
