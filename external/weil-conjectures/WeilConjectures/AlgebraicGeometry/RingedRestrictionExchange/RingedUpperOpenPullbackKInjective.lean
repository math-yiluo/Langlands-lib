/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RingedRestrictionExchange.RingedExchangeChainUnit
public import WeilConjectures.AlgebraicGeometry.RingedRestrictionExchange.ProEtaleOpenPullbackKInjective

/-! # K-injective preservation along the upper side of an open square

## References

* Stacks Project, Tags 08FI and 09A5
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.RingedRestrictionExchange

attribute [local instance 30000]
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse
attribute [local irreducible] proEtaleRingModulePullback

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {sq : ChosenCartesianSquare g' f' f g}

/-- Upper pullback in a Cartesian square over an open immersion preserves K-injectives. -/
@[instance] theorem upper_pull_preservesKInjectiveComplexes
    (r : StrictTowerRingedSquare sq) [IsOpenImmersion g] :
    (upperPull r).PreservesKInjectiveComplexes := by
  have : IsOpenImmersion g' := by
    rw [← sq.hom_fst]
    infer_instance
  exact open_pullback_preservesKInjectiveComplexes g' r.RX r.RX' r.cg'

end AlgebraicGeometry.Scheme.RingedRestrictionExchange
