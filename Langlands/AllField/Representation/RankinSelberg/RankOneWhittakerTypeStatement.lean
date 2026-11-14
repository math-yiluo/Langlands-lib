import Langlands.Representation.RankinSelberg.RankOneWhittakerTypeStatement
import Langlands.AllField.Representation.RankinSelberg.AnalyticStatementSupplement
/-!
# Full Whittaker type of a rank-one quasicharacter

This module states an elementary certificate for the actual scalar
representation used in ramified rank-one enlargement. It contains no proof.
-/

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement QuotientHaarExistenceStatement RankOneWhittakerTypeStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear

universe uF

/-- Every continuous quasicharacter of a canonical p-adic field gives a
full Whittaker-type representation of GL(1), for any unitary additive
character. The carrier is the complex scalars and the action is the
published `rankOneCharacter`, with no smoothness premise. -/
def RankOneWhittakerTypeStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (χ : Quasicharacter F),
    IsOfWhittakerType 0 (standardCharacter ψ 0)
      (rankOneCharacter (χ : Fˣ →* ℂˣ))

end Langlands.AllField.RankinSelberg
