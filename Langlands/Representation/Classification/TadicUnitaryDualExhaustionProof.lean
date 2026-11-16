import Langlands.Representation.Classification.TadicExhaustionReductionProof
import Langlands.Representation.Classification.TadicBlockReductionProof
import Langlands.Representation.Classification.TadicRectangleHeadSocleDistinctProof
import Langlands.Representation.Classification.IrreducibleLanglandsHeadProductProof
import Langlands.Representation.Classification.MultisegmentHeadClassificationProof
import Langlands.Representation.Classification.SpehUnitarizabilityProof

/-!
# Tadic's generic-free unitary-dual exhaustion

Tadic 1986, Theorem D(ii), exhaustion clause (with section 7.4, Theorem 7.5(ii) and
Appendix A.10): every irreducible unitarizable smooth representation of `GL_(n+1)`
over a p-adic field is isomorphic to the entire normalized product of finitely many
Tadic building blocks. The proof applies the published reduction
`tadicExhaustionReduction` to published proofs of all its ingredients.
-/

namespace Langlands.Classification

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- **Tadic 1986, Theorem D(ii), exhaustion.** Every actual irreducible unitarizable
smooth representation of positive rank is isomorphic to the entire finite normalized
upper-block induction of actual Tadic building blocks. -/
theorem tadicUnitaryDualExhaustion : TadicUnitaryDualExhaustion.{uF, uV} F T :=
  tadicExhaustionReduction.{uF, uV} F T
    ⟨tadicBlockReduction.{uF, uV} F T,
      TadicRectangleHeadSocle.tadicRectangleHeadSocleDistinct.{uF, uV} F T,
      irreducibleLanglandsHeadProduct.{uF, uV} F T⟩
    (spehUnitarizability.{uF, uV} F T)
    (multisegmentHeadClassification.{uF, uV} F T)

end Langlands.Classification
