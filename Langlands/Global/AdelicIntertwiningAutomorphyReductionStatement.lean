import Langlands.Global.AdelicIntertwiningAutomorphyStatement

/-! # Uniform automorphy of intertwining integrals from its two remaining analytic parts

The implication from `IntertwiningSmoothSlicesStatement` and
`IntertwiningUniformCenterIdealStatement` to `IntertwiningUniformAutomorphyStatement`: the
remaining conditions of an automorphic form on `V(𝔸)M'(F) \ G(𝔸)` (left invariance, continuity,
compact finiteness, a finite level and moderate growth) hold for every sufficiently regular
parameter without further input. -/

universe u

set_option autoImplicit false

namespace Langlands.Global

/-- Smoothness of the infinite slices (`IntertwiningSmoothSlicesStatement`, Mœglin–Waldspurger
II.1.6 (i)) and one center ideal for all regular parameters
(`IntertwiningUniformCenterIdealStatement`, Bernstein–Lapid, proof of the Lemma in §8.2) imply
uniform automorphy of intertwining integrals (`IntertwiningUniformAutomorphyStatement`). -/
def IntertwiningUniformAutomorphyReductionStatement : Prop :=
  IntertwiningSmoothSlicesStatement.{u} → IntertwiningUniformCenterIdealStatement.{u} →
    IntertwiningUniformAutomorphyStatement.{u}

end Langlands.Global
