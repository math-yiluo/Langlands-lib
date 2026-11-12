import Langlands.Correspondence.HenniartCorrespondenceInduction
import Langlands.Correspondence.HenniartSurjectivityStepProof
import Langlands.Correspondence.HenniartConductorFinitenessProof
import Langlands.Correspondence.SupercuspidalLevelFinitenessProof
import Langlands.Representation.RankinSelberg.PairEpsilonExponentProof

/-!
# Henniart's route with the surjectivity step and the finiteness discharged

`SupercuspidalCorrespondenceHenniartInductionStatement` takes the surjectivity
step and the conductor finiteness of candidate sets as hypotheses. The published
reductions `surjectivityStepReduction`,
`supercuspidalEpsilonConductorFinitenessReduction`, `pairEpsilonExponentReduction`
and `supercuspidalLevelFinitenessReduction` replace them by their own inputs.
-/

namespace Langlands.Henniart.Extension

open Langlands.Correspondence LocalFactor LocalFactor.CommonClosure

universe uK uW uV

/-- Henniart's route to the all-field supercuspidal correspondence from its
remaining inputs: candidate existence, normalized local reciprocity, local
constants for every normalized family, the surjectivity assertion of Henniart's
numerical theorem, the conductor exponent of local constants (Tate (3.4.5),
Deligne (5.5.2)), the equal-rank change of additive character for pair epsilon
factors, the conductor exponent of generic representations (JPSS (5.1)) and
compact-open finiteness of supercuspidal classes (Bernstein–Zelevinsky 4.15). -/
def SupercuspidalCorrespondenceHenniartFinalStatement : Prop :=
  CandidateExistenceStatement.{uK, uW, uV, uW, uK} →
  LocalClassField.CommonClosureReciprocityExistence.{uK} →
  (∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (eC : ReciprocityFamily K),
    NonabelianSystem.Exists.{uK, uW} K eC) →
  NumericalSurjectivityStatement.{uK, uW, uV} →
  (∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p),
    ConductorExponent.SpectralConductorStatement.{uK, uW} K) →
  RankinSelberg.EqualRankEpsilonCharacterChangeStatement.{uK, uV, 0} →
  Conductor.ConductorExponentStatement.{uK, uV} →
  SupercuspidalCompactOpenFinitenessStatement.{uK, uV} →
  SupercuspidalCorrespondenceStatement.{uK, uW, uV}

/-- Proof of `SupercuspidalCorrespondenceHenniartFinalStatement`. -/
theorem supercuspidalCorrespondenceHenniartFinal :
    SupercuspidalCorrespondenceHenniartFinalStatement.{uK, uW, uV} := by
  intro hCE hrec hsys hnum hSC hEq hJPSS hcompact
  have hBHK : RankinSelberg.PairEpsilonExponentStatement.{uK, uV, 0} :=
    RankinSelberg.pairEpsilonExponentReduction hEq
  exact supercuspidalCorrespondenceHenniartInduction hCE
    (surjectivityStepReduction hCE hrec hsys hnum hSC hBHK hJPSS)
    (supercuspidalEpsilonConductorFinitenessReduction
      (supercuspidalLevelFinitenessReduction hcompact) hBHK hJPSS)
    hrec hsys

end Langlands.Henniart.Extension
