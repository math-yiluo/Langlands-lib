import Langlands.Correspondence.HenniartCorrespondenceFiveInputs
import Langlands.LocalFactor.NonabelianSystemExistsProof
import Langlands.LocalFactor.SpectralConductorRankOneProof

/-!
# Henniart's route with local constants and rank-one conductor transport discharged

`SupercuspidalCorrespondenceHenniartFiveInputsStatement` takes the existence of local
constants for every normalized family (`NonabelianSystem.Exists`) and rank-one conductor
transport in the common closure (`SpectralConductor.CommonClosureRankOneConductorStatement`)
among its five hypotheses. They are proved by the published `NonabelianSystem.exists_system`
and `SpectralConductor.commonClosureRankOneConductor`, which leaves three hypotheses.
-/

namespace Langlands.Henniart.Extension

open Langlands.Correspondence LocalFactor

universe uK uW uV

/-- Henniart's route to the all-field supercuspidal correspondence from candidate
existence, the surjectivity assertion of Henniart's numerical theorem, and the conductor
exponent of generic representations (JPSS (5.1)). -/
def SupercuspidalCorrespondenceHenniartThreeInputsStatement : Prop :=
  CandidateExistenceStatement.{uK, uW, uV, uW, uK} →
  NumericalSurjectivityStatement.{uK, uW, uV} →
  Conductor.ConductorExponentStatement.{uK, uV} →
  SupercuspidalCorrespondenceStatement.{uK, uW, uV}

/-- Proof of `SupercuspidalCorrespondenceHenniartThreeInputsStatement`. -/
theorem supercuspidalCorrespondenceHenniartThreeInputs :
    SupercuspidalCorrespondenceHenniartThreeInputsStatement.{uK, uW, uV} := by
  intro hCE hnum hJPSS
  exact supercuspidalCorrespondenceHenniartFiveInputs hCE
    (fun p _ K eC => NonabelianSystem.exists_system K eC) hnum
    (SpectralConductor.commonClosureRankOneConductor) hJPSS

end Langlands.Henniart.Extension
