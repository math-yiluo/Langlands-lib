/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleSheaf
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement

/-!
# Intrinsic constructibility in the site coefficient universe

The existing small-coefficient predicate is re-exported. This interface permits finite
coefficients in Type (u+1), as required by the recorded adic tower. Finite stalks of a
locally constant sheaf are equivalently expressed by finite constant modules on a
refinement of its trivializing covering. Restrictions retain their actual inverse-image
coefficient sheaves and are linear over those sheaves.

## References

* Stacks Tags 09AI and 09AJ
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Intrinsic finite-stratification constructibility for a finite coefficient ring in the
site object universe. Each restricted sheaf is locally a finite constant module; this is
local constancy with finite geometric stalks. The positive number of strata includes the
empty scheme by a single empty stratum. No etale-origin condition is part of this notion. -/
def IsConstructibleProEtaleCoefficientModuleSheaf
    (Y : Scheme.{u}) (A : Type (u + 1)) [CommRing A] [Finite A]
    (F : pbcModules Y (adicLisseConstantRing Y A)) : Prop :=
  ∃ S : Stratification Y, 0 < S.n ∧
    (∀ i : Fin S.n, Topology.IsConstructible (S.stratum i)) ∧
    ∀ i : Fin S.n,
      IsRelativelyFiniteLisseModule (S.immersion i) A
        ((proEtaleModuleInverseImage (S.immersion i) (adicLisseConstantRing Y A)).obj F)

end AlgebraicGeometry.Scheme
