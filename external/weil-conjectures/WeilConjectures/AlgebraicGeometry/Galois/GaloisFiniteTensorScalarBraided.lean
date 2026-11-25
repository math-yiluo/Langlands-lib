/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Galois.GaloisLisseCorrespondenceData
import WeilConjectures.ConstructibleSheaf.Biproduct
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal

/-! # Braided tensor component of the finite Galois comparison

Source: Stacks Project, Tag 0DV5 (3), and the blueprint
`proposition-lattices-representations-normal-scheme`, proof steps 4 and 5 (blueprint:
new-d9-galois-finite-tensor-scalar-braided). -/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry Opposite
open MonoidalCategory
open scoped TensorProduct FintypeCatDiscrete

namespace AlgebraicGeometry.Scheme

noncomputable section

section Stalk

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  (y : Spec (.of Ω) ⟶ Y) {R : Type (u + 1)} [CommRing R]

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

-- The canonical tensorator, expressed before sheafification.
end Stalk

-- Coherence lifts once the structure isomorphisms intertwine the actions.
end

end AlgebraicGeometry.Scheme
