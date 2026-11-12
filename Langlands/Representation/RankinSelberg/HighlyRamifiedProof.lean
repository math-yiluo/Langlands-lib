import Langlands.Representation.RankinSelberg.HighlyRamifiedStatement
import Langlands.Representation.RankinSelberg.HighlyRamified.EssentialPairInputProof
import Langlands.Representation.RankinSelberg.HighlyRamified.KirillovShell
import Langlands.Representation.RankinSelberg.UniformRankOneTwistProof
import Langlands.Representation.Whittaker.CompletenessProof

/-!
# Highly ramified gamma stability

Proof of `HighlyRamifiedGammaStabilityStatement` (Jacquet and Shalika 1985, Proposition
(4.1), for generic pairs). The Library reduces it to the adjacent-rank step
(`highlyRamifiedGammaStability_of_adjacentStep`, `adjacentStep`), whose inputs are the
completeness lemma (`whittakerCompleteness`), the uniform rank-one statement
(`uniformRankOneTwist`), the Kirillov shell input (`kirillovShellInput`) and the essential
pair input, proved in `HighlyRamified.EssentialPairInputProof`.
-/

namespace Langlands.RankinSelberg

universe uF uV uW

/-- **Jacquet–Shalika 1985, Proposition (4.1)**, for generic pairs: highly ramified gamma
stability. -/
theorem highlyRamifiedGammaStability : HighlyRamifiedGammaStabilityStatement.{uF, uV, uW} :=
  HighlyRamified.highlyRamifiedGammaStability_of_adjacentStep
    UniformRankOneTwist.uniformRankOneTwist.{uF, max uF uV uW}
    UniformRankOneTwist.uniformRankOneTwist.{uF, uV}
    (HighlyRamified.adjacentStep
      Whittaker.CompletenessProof.whittakerCompleteness.{uF, max uF uV uW}
      (fun n => HighlyRamified.essentialPairInput_of_uniformRankOne
        UniformRankOneTwist.uniformRankOneTwist.{uF, max uF uV uW} n)
      HighlyRamified.kirillovShellInput.{uF, max uF uV uW})

end Langlands.RankinSelberg
