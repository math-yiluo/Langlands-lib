/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteReduction.FiniteReductionSystem
import WeilConjectures.AlgebraicGeometry.FiniteReduction.FiniteReductionRestrictTensor

/-!
# Flat models under surjective extension of constant scalars

Source: Stacks Project, Tag 05V4 and Tag 08G1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

namespace AlgebraicGeometry.FiniteReduction

section Site
variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C)
    {A B : Type (u + 1)} [CommRing A] [CommRing B]

end Site
end AlgebraicGeometry.FiniteReduction
