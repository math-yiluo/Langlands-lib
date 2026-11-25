/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.CategoryTheory.Sites.FlatLocalRelations

import WeilConjectures.CategoryTheory.DerivedCategory.ProEtaleCoefficients.DerivedMonoidalClosed
import WeilConjectures.CategoryTheory.DerivedModuleFreeGeneration
import WeilConjectures.CategoryTheory.DerivedCategory.Coproducts
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ShiftComparison
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapShift
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidal
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMonoidal
import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare
import Mathlib.CategoryTheory.Triangulated.Adjunction

set_option linter.privateModule false

/-!
# Projection on constant coefficients for coproduct-preserving compact support

## Implementation details

Compare the two exact coproduct-preserving coefficient functors, check the
projection on the tensor unit, and extend across the localizing generators of the derived
module category.

## References

* Stacks Project, Cohomology on Sites, projection formula and generation by free coefficient
  complexes
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Abelian Limits MonoidalCategory
open scoped CategoryTheory.Functor
universe uC uD

section ExactTensorComparison

variable {C : Type uC} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]
  {D : Type uD} [Category.{u + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [Abelian.HasFunctorialFlatResolution D]

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]

variable [F.leftDerivedFunctor.CommShift ℤ]
  [NatTrans.CommShift
    (F₁ := DerivedCategory.Qh ⋙ F.leftDerivedFunctor)
    (F₂ := F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    F.leftDerivedFunctorCounit ℤ]

end ExactTensorComparison

section ProjectionData

variable {C : Type uC} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]
  {D : Type uD} [Category.{u + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [Abelian.HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]

end ProjectionData

section CoefficientGeneration

variable {T : Type uC} [Category.{u + 1} T] [HasZeroObject T] [Preadditive T]
  [HasShift T ℤ] [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T]

end CoefficientGeneration

namespace AlgebraicGeometry
open Scheme
namespace ProEtale

section SupportTensor

variable (A : Type uC) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [UpperStarPreservesFlat A]

@[no_expose] private noncomputable def projectionMate {X Y : Scheme.{u}} (p : X ⟶ Y) :
    derivedTensorRightDerivedLowerStar A p ⟶
      rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar A p :=
  (derivedUpperStarLowerStarAdjunction A p).rightAdjointProjectionMap
    (upperStar A p).leftDerivedTensorComparison

end SupportTensor

end ProEtale
end AlgebraicGeometry
