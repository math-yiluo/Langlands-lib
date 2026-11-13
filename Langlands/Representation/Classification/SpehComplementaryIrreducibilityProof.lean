import Langlands.Representation.Classification.SpehUnitarizabilityReductionStatement
import Langlands.Representation.Classification.SpehIntegralLineSupportProof
import Langlands.Representation.Classification.SpehComplementaryLineSeparationProof
import Langlands.Representation.Classification.UnlinkedSocleProductIrreducibilityProof

/-! # Irreducibility of complementary products of Speh representations -/

namespace Langlands.Classification

open GeneralLinear PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The actual opposite complementary twists of a supplied Speh representation
have an irreducible normalized product for nonzero parameters in (-1/2, 1/2). -/
theorem spehComplementaryIrreducibility : SpehComplementaryIrreducibility.{uF, uV} F T := by
  let := T.topology
  intro d _hdisc S hS α hα hα0
  obtain ⟨ρ, s, hs, hsupport⟩ := spehIntegralLineSupport.{uF, uV} F T d S hS
  exact integralLineComplementaryIrreducibilityReduction.{uF, uV} F T
    (unlinkedSocleProductIrreducibility.{uF, uV} F T)
    d.degree (Nat.mul_pos d.length_pos d.rank_pos) S s hs ρ hsupport α hα hα0

end Langlands.Classification
