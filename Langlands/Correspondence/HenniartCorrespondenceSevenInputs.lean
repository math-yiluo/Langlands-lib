import Langlands.Correspondence.HenniartCorrespondenceFinal
import Langlands.Representation.RankinSelberg.EqualRankEpsilonCharacterChangeProof

/-!
# Henniart's route with the equal-rank change of character discharged

`SupercuspidalCorrespondenceHenniartFinalStatement` takes the equal-rank change of
additive character for pair epsilon factors as one of eight hypotheses. The
theorem `RankinSelberg.equalRankEpsilonCharacterChange` proves it at every
universe level, so seven hypotheses remain.
-/

namespace Langlands.Henniart.Extension

open Langlands.Correspondence LocalFactor LocalFactor.CommonClosure

universe uK uW uV

/-- Henniart's route to the all-field supercuspidal correspondence from its
seven remaining inputs: candidate existence, normalized local reciprocity, local
constants for every normalized family, the surjectivity assertion of Henniart's
numerical theorem, the conductor exponent of local constants (Tate (3.4.5),
Deligne (5.5.2)), the conductor exponent of generic representations (JPSS (5.1))
and compact-open finiteness of supercuspidal classes (Bernstein–Zelevinsky 4.15). -/
def SupercuspidalCorrespondenceHenniartSevenInputsStatement : Prop :=
  CandidateExistenceStatement.{uK, uW, uV, uW, uK} →
  LocalClassField.CommonClosureReciprocityExistence.{uK} →
  (∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (eC : ReciprocityFamily K),
    NonabelianSystem.Exists.{uK, uW} K eC) →
  NumericalSurjectivityStatement.{uK, uW, uV} →
  (∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p),
    ConductorExponent.SpectralConductorStatement.{uK, uW} K) →
  Conductor.ConductorExponentStatement.{uK, uV} →
  SupercuspidalCompactOpenFinitenessStatement.{uK, uV} →
  SupercuspidalCorrespondenceStatement.{uK, uW, uV}

/-- Proof of `SupercuspidalCorrespondenceHenniartSevenInputsStatement`. -/
theorem supercuspidalCorrespondenceHenniartSevenInputs :
    SupercuspidalCorrespondenceHenniartSevenInputsStatement.{uK, uW, uV} :=
  fun hCE hrec hsys hnum hSC hJPSS hcompact =>
    supercuspidalCorrespondenceHenniartFinal hCE hrec hsys hnum hSC
      RankinSelberg.equalRankEpsilonCharacterChange.{uK, uV, 0} hJPSS hcompact

end Langlands.Henniart.Extension
