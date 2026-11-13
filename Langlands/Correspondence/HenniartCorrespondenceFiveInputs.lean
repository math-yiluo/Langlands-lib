import Langlands.Correspondence.HenniartCorrespondenceRankOneInputs
import Langlands.LocalFactor.Ramification.InertiaConductorRefinementProof
import Langlands.LocalFactor.Ramification.InertiaConductorProfile

/-!
# Henniart's route with refinement invariance of conductors discharged

`SupercuspidalCorrespondenceHenniartRankOneInputsStatement` takes refinement invariance
of presentation conductors (`Ramification.Padic.FiniteInertiaConductorRefinementStatement`)
among its six hypotheses. It is proved by
`Ramification.Padic.finiteInertiaConductorRefinement`, which leaves five hypotheses.
-/

namespace Langlands.Henniart.Extension

open Langlands.Correspondence LocalFactor LocalFactor.CommonClosure

universe uK uW uV

/-- Henniart's route to the all-field supercuspidal correspondence from candidate
existence, local constants for every normalized family, the surjectivity assertion of
Henniart's numerical theorem, rank-one conductor transport in the common closure, and
the conductor exponent of generic representations (JPSS (5.1)). -/
def SupercuspidalCorrespondenceHenniartFiveInputsStatement : Prop :=
  CandidateExistenceStatement.{uK, uW, uV, uW, uK} →
  (∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (eC : ReciprocityFamily K),
    NonabelianSystem.Exists.{uK, uW} K eC) →
  NumericalSurjectivityStatement.{uK, uW, uV} →
  (∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p),
    SpectralConductor.CommonClosureRankOneConductorStatement K) →
  Conductor.ConductorExponentStatement.{uK, uV} →
  SupercuspidalCorrespondenceStatement.{uK, uW, uV}

/-- Proof of `SupercuspidalCorrespondenceHenniartFiveInputsStatement`. -/
theorem supercuspidalCorrespondenceHenniartFiveInputs :
    SupercuspidalCorrespondenceHenniartFiveInputsStatement.{uK, uW, uV} := by
  intro hCE hsys hnum hR hJPSS
  exact supercuspidalCorrespondenceHenniartRankOneInputs hCE hsys hnum
    (fun p _ K A => Ramification.Padic.finiteInertiaConductorRefinement K A) hR hJPSS

end Langlands.Henniart.Extension
