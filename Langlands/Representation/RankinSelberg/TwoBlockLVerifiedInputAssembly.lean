import Langlands.Representation.RankinSelberg.TwoBlockLConditionalAssembly
import Langlands.Representation.RankinSelberg.TwoBlockUniverseTransport
import Langlands.Representation.RankinSelberg.EqualRankRankOneExtensionDivisibilityProof
import Langlands.Representation.RankinSelberg.EqualRankFactorSwapProof
import Langlands.Representation.RankinSelberg.RankOneWhittakerTypeProof
import Langlands.HarmonicAnalysis.UnboundedConductorProof

/-!
# Published inputs for the two-block L-polynomial descent

The available inputs are proved from imported Library theorems. The final
implication retains the three analytic bases, restricted reverse divisibility,
and high-ramification vanishing as explicit hypotheses.
-/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockLVerifiedInputAssembly

open HarmonicAnalysis

universe uF uV uW u

/-- The endpoint's scalar lift is definitionally the lift in the conditional
descent, so the published closed endpoint supplies its fieldwise input. -/
theorem equalRankReverseAt {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ) :
    TwoBlockLConditionalAssembly.EqualRankReverseAt.{uF, uV, uW} F ψ ν :=
  equalRankRankOneExtensionLDivisibility.{uF, uV, uW} p F ψ ν

/-- The seven inputs already supplied by closed Library proofs, in the
carrier universe used by both descending inductions. -/
def AvailableInputs : Prop :=
  (∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ),
    TwoBlockLConditionalAssembly.EqualRankReverseAt.{uF, max uF u, max uF u} F ψ ν) ∧
  SymmetricLPolynomialExistenceStatement.{uF, max uF u, max uF u} ∧
  EqualRankFactorSwapStatement.{uF, max uF u, max uF u} ∧
  NormalizedProductWhittakerTypeStatement.{uF, max uF u} ∧
  RankOneWhittakerTypeStatement.{uF} ∧
  EqualRankFactorSwapStatement.{uF, 0, max uF u} ∧
  PadicQuasicharacterUnboundedConductorStatement.{uF}

/-- No analytic proposition is assumed in this package of available inputs. -/
theorem availableInputs : AvailableInputs.{uF, u} :=
  ⟨fun _p _ F ψ ν => equalRankReverseAt F ψ ν,
    symmetricLPolynomialExists.{uF, max uF u, max uF u},
    equalRankFactorSwap.{uF, max uF u, max uF u},
    normalizedProductWhittakerType.{uF, max uF u},
    rankOneWhittakerType.{uF},
    equalRankFactorSwap.{uF, 0, max uF u},
    padicQuasicharacterUnboundedConductor.{uF}⟩

/-- The remaining five analytic inputs suffice for the original target with
independent field, test-carrier, and block-carrier universes. -/
theorem twoBlockLFactorMultiplicativity_of_remainingInputs
    (hdominant :
      TwoBlockLDominantRankStatement.{uF, max uF uV uW, max uF uV uW})
    (hadjacent :
      TwoBlockLAdjacentRankStatement.{uF, max uF uV uW, max uF uV uW})
    (hrankBase :
      TwoBlockLRankOneStatement.{uF, max uF uV uW, max uF uV uW})
    (hrestricted :
      RankOneExtensionLDivisibilityStatement.{uF, max uF uV uW, max uF uV uW})
    (hram :
      WhittakerTypeHighlyRamifiedLVanishingStatement.{uF, 0, max uF uV uW}) :
    TwoBlockLFactorMultiplicativityStatement.{uF, uV, uW} := by
  obtain ⟨hequal, hexists, hswap, htype, hrankOne, hscalarSwap, hcharacters⟩ :=
    availableInputs.{uF, max uV uW}
  apply twoBlockLFactorMultiplicativity_of_commonUniverse.{uF, uV, uW}
  exact TwoBlockLConditionalAssembly.twoBlockLMultiplicativity_of_inputs_commonUniverse.{uF, max uV uW}
    hdominant hadjacent hrankBase hrestricted hequal hexists hswap htype hram
    hrankOne hscalarSwap hcharacters

end Langlands.RankinSelberg.TwoBlockLVerifiedInputAssembly
