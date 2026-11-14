import Langlands.Representation.RankinSelberg.RankOneCharacterReductionStatement
import Langlands.AllField.Representation.RankinSelberg.AnalyticStatementSupplement
/-!
# Reduction of full rank-one Whittaker type to a quasicharacter

This module states the arbitrary-carrier reduction to the actual continuous
quasicharacter representation on complex scalars. It contains no proof.
-/

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement QuotientHaarExistenceStatement RankOneCharacterReductionStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis
open Langlands.Whittaker

universe uF uV

/-- Every full Whittaker-type representation of GL(1), on an arbitrary complex
module, is equivalent to the published scalar action of a continuous
quasicharacter. The field carries its canonical p-adic topology. -/
def RankOneCharacterReductionStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear (0 + 1) F) V),
    IsOfWhittakerType 0 (standardCharacter ψ 0) π →
      ∃ χ : Quasicharacter F,
        Nonempty (π.Equiv (rankOneCharacter (χ : Fˣ →* ℂˣ)))

end Langlands.AllField.RankinSelberg
