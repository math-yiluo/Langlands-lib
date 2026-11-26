import Langlands.Global.AdelicParameterTwistAutomorphyStatement
import Langlands.Global.AdelicParameterTwistCenterFiniteStatement

/-! # Automorphy of twists from center finiteness of twists

The automorphy of the twists `φ_λ` of Bernstein–Lapid §2.2 (`ParameterTwistAutomorphyStatement`)
follows from its `𝔷`-finiteness part (`ParameterTwistCenterFiniteStatement`). -/

universe u

set_option autoImplicit false

namespace Langlands.Global

/-- `ParameterTwistCenterFiniteStatement` implies `ParameterTwistAutomorphyStatement`: the other
conditions of an automorphic form on `U_I(𝔸) M_I(F) \ G(𝔸)` (left invariance, smoothness,
finiteness under the archimedean part of `K` and moderate growth) pass from `φ` to `φ_λ`
without further input. -/
def ParameterTwistAutomorphyReductionStatement : Prop :=
  ParameterTwistCenterFiniteStatement.{u} → ParameterTwistAutomorphyStatement.{u}

end Langlands.Global
