import Langlands.Global.Factors.CuspidalPairPoleStatement
import Langlands.Global.Factors.CuspidalPairFunctionalEquationReduction
import Langlands.Global.Factors.CuspidalPairSemilocalRatioStatement
import Langlands.Global.Factors.CuspidalPairVerticalStripStatement
import Langlands.Global.RankinSelberg.CuspidalSlabPairingStatement

/-!
# Reduction of the poles of cuspidal pair L-functions to local and residue inputs

Proposition definition only: `CuspidalPairPoleStatement` (Getz–Hahn (2024), Theorem 11.7.1,
poles and vertical strips; Cogdell (2004), Theorems 4.1 and 4.2) follows from four inputs:
the existence of archimedean parameters, the residue clause of Cogdell (2004), Theorem 2.2,
the semi-local ratios of Cogdell (2004), §4, and the bound in vertical strips. See the paired
Markdown for the sources of each input and the proof route.
-/

noncomputable section

set_option autoImplicit false

universe u uQ

namespace Langlands.Global

/-- **Reduction of Getz–Hahn (2024), Theorem 11.7.1 (poles and vertical strips).**
The existence of archimedean parameters of cuspidal realizations
(`CuspidalArchimedeanParameterExistenceStatement`), the residue clause of Cogdell (2004),
Theorem 2.2 (`RankinSelbergGlobal.CuspidalSlabPairingStatement`), the semi-local ratios of the
partial Rankin–Selberg integrals (`CuspidalPairSemilocalRatioStatement`) and the bound in
vertical strips of continued completed L-functions (`CuspidalPairVerticalStripStatement`)
imply `CuspidalPairPoleStatement`. -/
def CuspidalPairPoleReductionStatement : Prop :=
  CuspidalArchimedeanParameterExistenceStatement.{u} →
    RankinSelbergGlobal.CuspidalSlabPairingStatement.{u, uQ} →
    CuspidalPairSemilocalRatioStatement.{u, uQ} →
    CuspidalPairVerticalStripStatement.{u, uQ} →
    CuspidalPairPoleStatement.{u, uQ}

end Langlands.Global
