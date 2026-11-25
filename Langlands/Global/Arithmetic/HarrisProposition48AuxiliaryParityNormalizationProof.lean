import Langlands.Global.Arithmetic.HarrisProposition48AuxiliaryParityNormalizationReductionProof
import Langlands.Global.Arithmetic.HarrisNormTwistInfinityProof
import Langlands.Global.Arithmetic.HarrisCMNormConjugationProof
import Langlands.Global.Arithmetic.HarrisProposition48PlaceNormTwistProof
import Langlands.Global.Arithmetic.HarrisGeneralPositionAmbientTwistProof

/-!
# Auxiliary-place parity normalization in Harris, Proposition 4.8

A proof of `Langlands.Global.Harris.Proposition48AuxiliaryParityNormalizationStatement`: the
Library's reduction `proposition48AuxiliaryParityNormalizationReduction` applied to the infinity
and CM norm transport (`normTwistInfinity`, `cmNormConjugation`, at the number-field universes
`0` and `0, 0` fixed by the reduction), to the transport of actual finite components
(`proposition48PlaceNormTwist`) and to the preservation of general position under an ambient Weil
twist (`generalPositionAmbientTwist`). See the paired Markdown.
-/

universe uF

namespace Langlands.Global.Harris

/-- **Parity normalization at the auxiliary place.** For every bundled Proposition 4.8 problem
valid at the auxiliary place for the parity `b`, there are a genuine Hecke character `ν` of the
base field and a new auxiliary local character `χs` that normalize the infinity parity
(`IsAuxiliaryParityNormalization`). -/
theorem proposition48AuxiliaryParityNormalization :
    Proposition48AuxiliaryParityNormalizationStatement.{uF} :=
  proposition48AuxiliaryParityNormalizationReduction.{uF} normTwistInfinity.{0}
    cmNormConjugation.{0, 0} proposition48PlaceNormTwist.{uF} generalPositionAmbientTwist.{uF}

end Langlands.Global.Harris
