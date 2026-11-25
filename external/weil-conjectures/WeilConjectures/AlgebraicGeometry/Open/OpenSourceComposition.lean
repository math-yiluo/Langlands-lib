/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement

/-! Source-open normalization of compact-support composition. -/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory

namespace AlgebraicGeometry.Etale

-- Keep signature checking from unfolding the compactification and derived constructions.
attribute [local irreducible] lowerStar openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor rightDerivedLowerShriekIso
  rightDerivedLowerShriekOfCompactificationIso unboundedEtaleLowerShriekCompIso

end AlgebraicGeometry.Etale
