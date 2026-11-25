import Langlands.Global.Arithmetic.HarrisProposition48ParityNormalizationReductionProof
import Langlands.Global.Arithmetic.HarrisProposition48AuxiliaryParityNormalizationProof
import Langlands.Global.Arithmetic.HarrisProposition48PlaceNormTwistProof

/-!
# Two-place parity normalization in Harris, Proposition 4.8

A proof of `Langlands.Global.Harris.Proposition48ParityNormalizationStatement`: the Library's
reduction `proposition48ParityNormalizationReduction` applied to the auxiliary-place
normalization `proposition48AuxiliaryParityNormalization` and to the transport of actual finite
components `proposition48PlaceNormTwist`. See the paired Markdown.
-/

universe uF

namespace Langlands.Global.Harris

/-- **Parity normalization for the complete datum.** For every bundled Proposition 4.8 problem
valid at the parity `b`, there are a genuine Hecke character `ν` of the base field and new local
characters `χ`, `χs` that normalize the infinity parity (`IsParityNormalization`). -/
theorem proposition48ParityNormalization : Proposition48ParityNormalizationStatement.{uF} :=
  proposition48ParityNormalizationReduction.{uF} proposition48AuxiliaryParityNormalization.{uF}
    proposition48PlaceNormTwist.{uF}

end Langlands.Global.Harris
