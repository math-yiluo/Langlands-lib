import Langlands.Representation.Unitary.HermitianWeightSequenceStatement
import Langlands.Representation.Unitary.HermitianNeighborhoodWeightProof

noncomputable section

namespace Langlands.Analysis

open MeasureTheory MeasureTheory.Measure Filter
open scoped NNReal Topology

universe uG

/-- Choose neighborhood weights along a decreasing countable local basis. -/
theorem hermitianWeightSequence : HermitianWeightSequenceStatement.{uG} := by
  intro G _ _ _ _ _ _ _ _ μ _ _ d hd
  obtain ⟨V, hV⟩ := (𝓝 (1 : G)).exists_antitone_basis
  have hex := fun n : ℕ => hermitianNeighborhoodWeight μ d hd (V n) (hV.mem n)
  choose f hcont hcompact hsupp hnonneg hint hmass hhermitian using hex
  refine ⟨f, fun n => ⟨hcont n, hcompact n, hnonneg n, hint n, hmass n, hhermitian n⟩, ?_⟩
  intro U hU
  obtain ⟨N, hNU⟩ := hV.mem_iff.mp hU
  filter_upwards [eventually_ge_atTop N] with n hn
  exact (hsupp n).trans ((hV.antitone hn).trans hNU)

end Langlands.Analysis
