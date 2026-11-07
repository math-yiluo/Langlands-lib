import Langlands.Representation.Classification.TadicExhaustionLemmasStatement
import Langlands.Representation.Classification.SpehUnitarizabilityStatement
import Langlands.Representation.Classification.MultisegmentClassificationStatement

/-!
# Tadić's exhaustion argument as an implication

Tadić's proof of Theorem A.10 (1986, printed pp.378-379) derives the exhaustion
of the unitary dual from Lemma 4.8(ii), Lemma 6.3, Corollary A.6(ii), Theorem A.8
and the classification of Langlands quotients by their multisegments.
The implication is stated as a proposition definition; nothing is proved here.
-/

namespace Langlands.Classification

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Tadić's reduction of Theorem D(ii) (exhaustion) to its ingredients: Lemma 4.8(ii),
Lemma 6.3 and Corollary A.6(ii) (`TadicExhaustionLemmaStatements`), Theorem A.8
(`SpehUnitarizability`) and the classification of Langlands heads by their
multisegments together imply `TadicUnitaryDualExhaustion`. -/
def TadicExhaustionReduction : Prop :=
  TadicExhaustionLemmaStatements.{uF, uV} F T → SpehUnitarizability.{uF, uV} F T →
    MultisegmentHeadClassification.{uF, uV} F T → TadicUnitaryDualExhaustion.{uF, uV} F T

end Langlands.Classification
