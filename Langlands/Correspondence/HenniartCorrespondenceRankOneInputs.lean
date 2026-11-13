import Langlands.Correspondence.HenniartCorrespondenceSixInputs
import Langlands.ClassFieldTheory.Local.CommonClosureExistenceProof
import Langlands.LocalFactor.SpectralConductorReduction

/-!
# Henniart's route with Tate's conductor formula reduced to rank one

`SupercuspidalCorrespondenceHenniartSixInputsStatement` takes normalized local
reciprocity and Tate's spectral conductor formula (Tate (3.4.5), Deligne (5.5.2))
among its six hypotheses. The first is proved in the Library
(`LocalClassField.commonClosureReciprocityExistence`). The second follows from
refinement invariance of presentation conductors and rank-one conductor transport
at the intermediate fields of the common closure
(`LocalFactor.SpectralConductor.spectralConductorRankOneReduction`).
-/

namespace Langlands.Henniart.Extension

open Langlands.Correspondence LocalFactor LocalFactor.CommonClosure

universe uK uW uV

/-- Henniart's route to the all-field supercuspidal correspondence from candidate
existence, local constants for every normalized family, the surjectivity assertion of
Henniart's numerical theorem, refinement invariance of presentation conductors,
rank-one conductor transport in the common closure, and the conductor exponent of
generic representations (JPSS (5.1)). -/
def SupercuspidalCorrespondenceHenniartRankOneInputsStatement : Prop :=
  CandidateExistenceStatement.{uK, uW, uV, uW, uK} →
  (∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (eC : ReciprocityFamily K),
    NonabelianSystem.Exists.{uK, uW} K eC) →
  NumericalSurjectivityStatement.{uK, uW, uV} →
  (∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p)
    (A : FiniteRepresentation.{0, uK, max uK uW} ℂ (Weil.Local.localWeilGroup K)),
    Ramification.Padic.FiniteInertiaConductorRefinementStatement.{uK, max uK uW} K A) →
  (∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p),
    SpectralConductor.CommonClosureRankOneConductorStatement K) →
  Conductor.ConductorExponentStatement.{uK, uV} →
  SupercuspidalCorrespondenceStatement.{uK, uW, uV}

/-- Proof of `SupercuspidalCorrespondenceHenniartRankOneInputsStatement`. -/
theorem supercuspidalCorrespondenceHenniartRankOneInputs :
    SupercuspidalCorrespondenceHenniartRankOneInputsStatement.{uK, uW, uV} := by
  intro hCE hsys hnum href hR hJPSS
  exact supercuspidalCorrespondenceHenniartSixInputs hCE
    LocalClassField.commonClosureReciprocityExistence.{uK} hsys hnum
    (fun p _ K => SpectralConductor.spectralConductorRankOneReduction.{uK, uW} K
      (href p K) (hR p K)) hJPSS

end Langlands.Henniart.Extension
