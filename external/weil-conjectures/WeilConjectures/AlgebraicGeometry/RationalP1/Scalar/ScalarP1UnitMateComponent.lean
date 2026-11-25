/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.RationalP1ScalarChernMaps
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DerivedExchangeExactNormalization
import WeilConjectures.CategoryTheory.ShiftedCompositeComparison
import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.Algebra.Ring.Int.Defs
import WeilConjectures.AlgebraicGeometry.RationalP1.Tate.RationalTateLineComposition
import WeilConjectures.AlgebraicGeometry.RationalP1.Ambient.AmbientSquareAssembly
import WeilConjectures.AlgebraicGeometry.RationalP1.DerivedCalculationInstances
import WeilConjectures.AlgebraicGeometry.RationalP1.Ambient.AmbientTwistedUnitMate
import WeilConjectures.AlgebraicGeometry.RationalP1.ShiftedLineSquare
import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.ScalarTraceEquation
import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.ScalarComponentFromTrace

/-! # The unit component of the scalar exchange mate

## Implementation details

The completed Chern data is omitted from the unit component, as it does not enter the
component equation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local instance 30000] CategoryTheory.sheafIsAbelian

/-- The scalar exchange carries the twisted unit to the twisted unit. -/
theorem scalar_p1_unit_mate_component
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))] :
    let Λ := (coefficient l c).X
    let L := line l c
    let T := fun X : Scheme.{u} ↦
      ((DerivedCategory.singleFunctor (Modules Λ X) 0).obj (L X)) ⟦(2 : ℤ)⟧
    let uq := scalarTwistedUnit Λ (ProjectiveLine Y ↘ Y) (T Y) (T (ProjectiveLine Y))
      (scalarQLineIso l c k p hpl Y)
    let u₂ := scalarTwistedUnit Λ (secondProjection Y)
      (T (ProjectiveLine Y)) (T (diagonalSurface Y)) (secondLineComparison l c k p hpl Y)
    let F := moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)
    F.map uq ≫ secondTraceExchange l c k p hpl Y =
        (scalarQLineIso l c k p hpl Y).hom ≫ u₂  := by
  apply scalar_component_from_trace l c k p hpl Y
  exact scalar_trace_equation l c k p hpl Y

end AlgebraicGeometry.ProEtale.RationalP1
