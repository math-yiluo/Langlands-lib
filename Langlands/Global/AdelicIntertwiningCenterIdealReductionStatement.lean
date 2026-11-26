import Langlands.Global.AdelicIntertwiningAutomorphyStatement
import Langlands.Global.AdelicLeviCenterTransferStatement
import Langlands.Global.AdelicIntertwiningStabilizerModulusStatement

/-! # The uniform center ideal from the Levi transfer and the Haar factor

`IntertwiningUniformCenterIdealReductionStatement` asserts that the normalized Harish-Chandra
transfer of the center to the target Levi subgroup, common to the two Weyl-conjugate parabolics
(`LeviRestrictionCenterTransferStatement`), and the Haar factor of a Levi conjugation in the
intertwining integral (`IntertwiningStabilizerModulusStatement`) imply that one ideal of finite
codimension in the center annihilates all regular intertwining integrals
(`IntertwiningUniformCenterIdealStatement`). -/

universe u

namespace Langlands.Global

/-- The Levi transfer and the Haar factor imply the uniform center ideal of Bernstein–Lapid §8.2. -/
def IntertwiningUniformCenterIdealReductionStatement : Prop :=
  LeviRestrictionCenterTransferStatement.{u} → IntertwiningStabilizerModulusStatement.{u} →
    IntertwiningUniformCenterIdealStatement.{u}

end Langlands.Global
