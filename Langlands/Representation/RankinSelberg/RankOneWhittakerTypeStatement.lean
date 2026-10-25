import Langlands.Representation.RankinSelberg.LocalFactor
import Langlands.Representation.RankinSelberg.AnalyticStatement

/-!
# Full Whittaker type of a rank-one quasicharacter

This module states an elementary certificate for the actual scalar
representation used in ramified rank-one enlargement. It contains no proof.
-/

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker GeneralLinear

universe uF

/-- Every continuous quasicharacter of a canonical p-adic field gives a
full Whittaker-type representation of GL(1), for any unitary additive
character. The carrier is the complex scalars and the action is the
published `rankOneCharacter`, with no smoothness premise. -/
def RankOneWhittakerTypeStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (χ : letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier),
    letI := F.canonicalTopologicalData.topology
    IsOfWhittakerType 0 (standardCharacter ψ 0)
      (rankOneCharacter (χ : F.Carrierˣ →* ℂˣ))

end Langlands.RankinSelberg
