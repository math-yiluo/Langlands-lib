/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.RationalP1ScalarChernMaps
public import WeilConjectures.AlgebraicGeometry.RationalP1.DerivedCalculationInstances
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DerivedExchangeExactNormalization
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing
attribute [local instance 30000] CategoryTheory.sheafIsAbelian
attribute [local instance 30000] cachedModuleClosed
attribute [local instance] CondensedRing.pullback_commShift
attribute [local irreducible] coefficient line firstProjection secondProjection square
attribute [local irreducible] condensedAmbientExchange
/-- The explicit second-trace exchange equality used by the scalar component.
It is packaged as a proposition so callers do not repeatedly normalize its
large categorical expression during elaboration. -/
structure ScalarTraceWitness
    (l : ℕ) [Fact l.Prime]
    (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (hpl : p ≠ l) (Y : Scheme.{u}) [Y.Over (Spec (.of k))] : Prop where
  exchange_eq : secondTraceExchange l c k p hpl Y =
      secondPretraceExchangeMap (coefficient l c).X Y
        (((DerivedCategory.singleFunctor (Modules (coefficient l c).X (ProjectiveLine Y))
          0).obj (line l c (ProjectiveLine Y))) ⟦(2 : ℤ)⟧) ≫
      (moduleObjectDerivedPushforward (coefficient l c).X (secondProjection Y)).map
        (firstLineComparisonForTrace l c k p hpl Y).hom

/-- Construct the packaged second-trace exchange witness from the trace
calculation in the scalar P1 square. -/
theorem scalar_trace_equation
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))] :
    ScalarTraceWitness l c k p hpl Y := by
  constructor
  unfold secondTraceExchange
  rfl
end AlgebraicGeometry.ProEtale.RationalP1
