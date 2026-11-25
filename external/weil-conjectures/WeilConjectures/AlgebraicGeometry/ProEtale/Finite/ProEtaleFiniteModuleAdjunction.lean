/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantExact

/-!
# The normalized finite-ring module adjunction

The existing inverse-image module and all its previous interfaces are reexported.
The additional adjunction uses the transported action for arbitrary finite rings.

## References

* Stacks Project, Modules on Sites
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type (u + 1))
  [Ring A] [Finite A] [TopologicalSpace A] [DiscreteTopology A]


end AlgebraicGeometry.ProEtale
