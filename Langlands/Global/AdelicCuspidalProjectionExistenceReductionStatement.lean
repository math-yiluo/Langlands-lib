import Langlands.Global.AdelicCuspidalProjectionExistenceStatement
import Langlands.Global.AdelicLeviCuspFormMajorantStatement
import Langlands.Global.AdelicCuspidalAnnihilator
import Langlands.Global.AdelicParabolicReproducingKernelStatement
import Langlands.Global.AdelicContinuousCuspidalProjectionStatement

/-! # Reduction of the existence of cuspidal projections to a continuous projection -/

universe u

set_option autoImplicit false

namespace Langlands.Global

/-- Weighted majorants of Levi cusp forms, the parabolic cuspidal vanishing criterion,
Harish-Chandra's reproducing kernel on parabolic quotients and the existence of continuous
cuspidal projections together give automorphic cuspidal projections. -/
def CuspidalProjectionExistenceReductionStatement : Prop :=
  LeviCuspFormPairingMajorantStatement.{u} → ParabolicCuspidalVanishingStatement.{u} →
    ParabolicReproducingKernelStatement.{u} → ContinuousCuspidalProjectionExistenceStatement.{u} →
      CuspidalProjectionExistenceStatement.{u}

end Langlands.Global
