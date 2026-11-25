/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClosedTestDerivedExchangeModel.ClosedTestDerivedExchangeMaps

/-! # Derived closed-unit evaluation and its naturality

Source: Stacks Project, proetale.tex, Tags 09BK and 09BL; sites-cohomology.tex, Tag 0D6F.
(blueprint: lem-sfb-nonaffine-closed-derived-evaluation). -/

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
