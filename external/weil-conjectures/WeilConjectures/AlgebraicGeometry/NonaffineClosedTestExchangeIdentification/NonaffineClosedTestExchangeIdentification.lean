/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClosedTestDerivedExchangeModel.ClosedTestDerivedExchangeMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.ClosedTestSectionSteps.ClosedTestSectionLocalization
import WeilConjectures.AlgebraicGeometry.ClosedTestSectionSteps.ClosedTestClosedEvaluation

/-!
# Closed lifted-test exchange for a qcqs, possibly nonaffine, source

The public affine-model module supplies canonical maps whose definitions have no
source-affineness assumption. Its already-general localization theorems are reused.
The closed-test criterion supplies covering, geometry and conservativity. The new
statements give the two normalized derived isomorphisms,
the identification with the actual ambient mate, and the compatibility clauses.

## References

* Stacks Project, Tags 09BK and 09BL, Tag 0D6F
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.NonaffineClosedTestExchangeIdentification

open ClosedTestDerivedExchangeModel ClosedTestSectionSteps

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Reuse the canonical shift structure on the named derived direct image. -/
instance pushCommShift {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (CondensedRing.moduleObjectDerivedPushforward Λ f).CommShift ℤ :=
  inferInstanceAs ((CondensedRing.lowerStar Λ f).rightDerivedFunctor.CommShift ℤ)

/-- Reuse the termwise shift structure on exact pullback. -/
instance pullCommShift {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pull Λ f).CommShift ℤ :=
  inferInstanceAs ((CondensedRing.upperStar Λ f).mapDerivedCategory.CommShift ℤ)

end AlgebraicGeometry.ProEtale.NonaffineClosedTestExchangeIdentification
