import Langlands.Correspondence.HenniartCorrespondenceSevenInputs
import Langlands.Correspondence.HenniartPadicConductorFinitenessProof

/-!
# Henniart's route with Bernstein–Zelevinsky finiteness proved over p-adic fields

`SupercuspidalCorrespondenceHenniartSevenInputsStatement` takes compact-open finiteness
of supercuspidal classes over every nonarchimedean local field (Bernstein–Zelevinsky
(1976), Corollary 4.15) as one of seven hypotheses. Henniart's route uses it only over
p-adic fields, through the finiteness of the candidate sets, and
`supercuspidalEpsilonConductorFinitenessPadicReduction` proves that finiteness without
it. Six hypotheses remain.
-/

namespace Langlands.Henniart.Extension

open Langlands.Correspondence LocalFactor LocalFactor.CommonClosure

universe uK uW uV

/-- Henniart's route to the all-field supercuspidal correspondence from its six
remaining inputs: candidate existence, normalized local reciprocity, local constants
for every normalized family, the surjectivity assertion of Henniart's numerical
theorem, the conductor exponent of local constants (Tate (3.4.5), Deligne (5.5.2)) and
the conductor exponent of generic representations (JPSS (5.1)). -/
def SupercuspidalCorrespondenceHenniartSixInputsStatement : Prop :=
  CandidateExistenceStatement.{uK, uW, uV, uW, uK} →
  LocalClassField.CommonClosureReciprocityExistence.{uK} →
  (∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (eC : ReciprocityFamily K),
    NonabelianSystem.Exists.{uK, uW} K eC) →
  NumericalSurjectivityStatement.{uK, uW, uV} →
  (∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p),
    ConductorExponent.SpectralConductorStatement.{uK, uW} K) →
  Conductor.ConductorExponentStatement.{uK, uV} →
  SupercuspidalCorrespondenceStatement.{uK, uW, uV}

/-- Proof of `SupercuspidalCorrespondenceHenniartSixInputsStatement`. -/
theorem supercuspidalCorrespondenceHenniartSixInputs :
    SupercuspidalCorrespondenceHenniartSixInputsStatement.{uK, uW, uV} := by
  intro hCE hrec hsys hnum hSC hJPSS
  have hBHK : RankinSelberg.PairEpsilonExponentStatement.{uK, uV, 0} :=
    RankinSelberg.pairEpsilonExponentReduction
      RankinSelberg.equalRankEpsilonCharacterChange.{uK, uV, 0}
  exact supercuspidalCorrespondenceHenniartInduction hCE
    (surjectivityStepReduction hCE hrec hsys hnum hSC hBHK hJPSS)
    (supercuspidalEpsilonConductorFinitenessPadicReduction hBHK hJPSS)
    hrec hsys

end Langlands.Henniart.Extension
