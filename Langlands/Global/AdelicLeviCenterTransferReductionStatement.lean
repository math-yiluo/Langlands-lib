import Langlands.Global.AdelicLeviCenterCongruenceStatement

/-! # The Levi transfer of the center from the normalized Harish-Chandra congruence

The normalized Harish-Chandra congruence of the center, common to two Weyl-conjugate
parabolics (`LeviRestrictionCenterCongruenceStatement`), implies the normalized Harish-Chandra
transfer of the center to their common Levi subgroup (`LeviRestrictionCenterTransferStatement`). -/

universe u

set_option autoImplicit false

namespace Langlands.Global

/-- The normalized Harish-Chandra congruence in the enveloping algebra of `G(F_∞)` implies the
transfer of the center to normalized Levi restrictions of functions on `G(F_∞)`: if for every
central `z` one element `y` of the enveloping algebra of `M'(F_∞)` satisfies both congruences of
`LeviRestrictionCenterCongruenceStatement`, then the same `y` realizes `z` on the normalized
restrictions `m ↦ δ_Q(m)^{-1/2} f(ι_Q(m) g)` and `m ↦ δ_P(c(m))^{-1/2} f(ι_P(m) g)` of
`LeviRestrictionCenterTransferStatement`. -/
def LeviRestrictionCenterTransferReductionStatement : Prop :=
  LeviRestrictionCenterCongruenceStatement.{u} → LeviRestrictionCenterTransferStatement.{u}

end Langlands.Global
