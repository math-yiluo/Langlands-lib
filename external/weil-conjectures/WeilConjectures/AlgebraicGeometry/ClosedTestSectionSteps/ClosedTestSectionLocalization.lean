/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClosedTestDerivedExchangeModel.ClosedTestDerivedExchangeMaps

/-! # Canonical section localization for arbitrary sources

Source: Stacks Project, sites-cohomology.tex, Tags 0D6E and 0D6F.
(blueprint: lem-sfb-nonaffine-proetale-section-localization). -/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ClosedTestSectionSteps

open ClosedTestDerivedExchangeModel

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

end AlgebraicGeometry.ProEtale.ClosedTestSectionSteps
