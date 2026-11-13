import Langlands.Representation.Classification.TadicBlockReductionAssembly

/-! Proof of `TadicBlockReductionFromInputs` (Tadić 1986, Lemma 4.8(ii), from its inputs). -/

namespace Langlands.Classification

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Tadić's Lemma 4.8(ii) follows from Bernstein's Theorem 2.5(i),(iii), Tadić's
Propositions 2.9 and 3.8, Zelevinsky's Proposition 8.5 and the Hermitian symmetry of
unitarizable representations. -/
theorem tadicBlockReductionFromInputs : TadicBlockReductionFromInputs.{uF, uV} F T :=
  TadicBlockReductionAssembly.tadicBlockReductionFromInputs F T

end Langlands.Classification
