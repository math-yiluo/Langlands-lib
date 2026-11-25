/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions

/-!
# Algebraically closed extension for reduced proper curves

Source: Stacks Project, Theorem 03SC, item (7), and Lemmas 03SD, 0A3Q, 03SG.
(blueprint: e1-algebraically-closed-cohomology-invariant)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.IsCurve

/-- Field extension invariance for reduced proper curves with constructible prime coefficients.
Source: Stacks Project, 03SC (theorem-vanishing-affine-curves), item (7).
(blueprint: e1-algebraically-closed-cohomology-invariant)

1. Apply `primeCoefficientCurveAssertions` to `f` and `F`. Its hypotheses are the existing
algebraically closed base field, reduced curve, prime `r`, and constructible sheaf; properness
is only needed in step 2.
It gives `IsCurve.Assertions (ULift (ZMod r)) f F`, uniformly in extensions and degrees.
2. Apply the C7 projection `Assertions.bijective_cohomologyMap_of_isProper` to this package,
`k'`, the pullback square `h`, and `q`. Properness is already an instance. The projection
uses the same `sheafCompose` forgetful functor and `Etale.cohomologyMap` as the conclusion,
so its type is the required bijectivity without any transport or additional hypothesis.
-/
theorem algebraicallyClosedCohomologyInvariant {k : Type u} [Field k] [IsAlgClosed k]
    {C C' : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f] [IsProper f] [IsReduced C]
    (k' : Type u) [Field k'] [IsAlgClosed k'] {ι : Spec (.of k') ⟶ Spec (.of k)}
    {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C} (h : IsPullback ι' f' f ι)
    {r : ℕ} [Fact r.Prime]
    (F : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))))
    [Scheme.IsConstructibleSheaf F] (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap ι'
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))
        AddCommGrpCat.{u + 1})).obj F) q) := by
  have hA : IsCurve.Assertions (ULift.{u + 1} (ZMod r)) f F :=
    primeCoefficientCurveAssertions f F
  exact IsCurve.Assertions.bijective_cohomologyMap_of_isProper hA k' h q

end AlgebraicGeometry.IsCurve
