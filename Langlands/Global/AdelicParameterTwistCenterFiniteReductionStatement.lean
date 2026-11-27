import Langlands.Automorphic.GroupSchemeLeviCenterRestriction
import Langlands.Global.AdelicParameterTwistCenterFiniteStatement

/-! # Center finiteness of twists from the finite Harish-Chandra transfer to a Levi

The implication from `ParabolicLeviCenterRestrictionStatement` (a finite algebra homomorphism
from the center of the enveloping algebra of `G(F_∞)` to that of a rational Levi `M(F_∞)`,
compatible with unnormalized restriction of left `V(F_∞)`-invariant functions) to
`ParameterTwistCenterFiniteStatement` (twists `φ_λ` of `𝔷`-finite functions on
`U_I(𝔸) \ G(𝔸)` are `𝔷`-finite). -/

noncomputable section

universe u

set_option autoImplicit false

namespace Langlands.Global

open Langlands.Automorphic.GroupSchemeFunctions

/-- The finite parabolic transfer of enveloping centers to a rational Levi implies that twisting
by `m_P^λ` preserves `𝔷`-finiteness on `U_I(𝔸) \ G(𝔸)`. This adapts the finite center transfer
of Mœglin–Waldspurger I.2.17 to the twist asserted in Bernstein–Lapid §2.2, p. 191. -/
def ParameterTwistCenterFiniteReductionStatement : Prop :=
  ParabolicLeviCenterRestrictionStatement.{u} → ParameterTwistCenterFiniteStatement.{u}

end Langlands.Global
