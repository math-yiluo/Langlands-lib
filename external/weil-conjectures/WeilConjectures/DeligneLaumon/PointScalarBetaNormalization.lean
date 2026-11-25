/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.ConstructiblePointComparisonData
public import WeilConjectures.DeligneLaumon.PointRealizationStandardCohomology

/-! # Normalization of the finite point scalar component

Source: the point coefficient convention, blueprint order 1509
(blueprint: lem-a1-point-scalar-beta-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u uC vC uB vB uD vD uA vA
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

attribute [local instance 2000] HasDerivedCategory.ofIsGrothendieckAbelian

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)

end WeilConjectures
