import Langlands.Representation.RankinSelberg.LocalFactor
import Langlands.Representation.RankinSelberg.AnalyticStatement

/-!
# Reduction of full rank-one Whittaker type to a quasicharacter

This module states the arbitrary-carrier reduction to the actual continuous
quasicharacter representation on complex scalars. It contains no proof.
-/

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker

universe uF uV

/-- Every full Whittaker-type representation of GL(1), on an arbitrary complex
module, is equivalent to the published scalar action of a continuous
quasicharacter. The field carries its canonical p-adic topology. -/
def RankOneCharacterReductionStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear (0 + 1) F.Carrier) V),
    letI := F.canonicalTopologicalData.topology
    IsOfWhittakerType 0 (standardCharacter ψ 0) π →
      ∃ χ : Quasicharacter F.Carrier,
        Nonempty (π.Equiv (rankOneCharacter (χ : F.Carrierˣ →* ℂˣ)))

end Langlands.RankinSelberg
