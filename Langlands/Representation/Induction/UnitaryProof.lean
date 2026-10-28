import Langlands.Representation.Induction.NormalizedIntegralForm
import Langlands.Representation.Induction.CompactScalarProof
import Langlands.Representation.Induction.UnitaryStatement
import Langlands.Representation.Tensor.UnitaryProof

/-! Invariant positive forms on actual normalized GL parabolic induction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory

namespace Langlands

universe uF uV

/-- Normalized parabolic induction preserves invariant positive forms on every
smooth actual representation of the block Levi. -/
theorem glNormalizedParabolicInductionUnitarity :
    GLNormalizedParabolicInductionUnitarityStatement.{uF, uV} := by
  intro p _ F T
  let := T.topology
  intro n hn B
  let := T.generalLinearTopologicalGroup n
  let := T.leviTopology B
  intro V _ _ σ _ hσ
  obtain ⟨K, _hK, hPK, hμ⟩ := glParabolicCompactScalarIntegral p F T n hn B
  let : MeasurableSpace K := borel K
  obtain ⟨μ, hHaar, _hprob, hscalarK⟩ := hμ
  let := hHaar
  obtain ⟨b⟩ := hσ
  exact ⟨T.normalizedIntegralForm B σ b K.toSubgroup μ hPK hscalarK⟩

/-- The actual normalized product induction of smooth unitarizable blocks is
unitarizable, using the positive form on their full algebraic tensor product. -/
theorem glNormalizedProductInductionUnitarity :
    GLNormalizedProductInductionUnitarityStatement.{uF, uV} := by
  intro p _ F T
  let := T.topology
  intro n hn B σ hσ
  have ht : IsUnitarizable (B.blockTensor (fun i => (σ i).representation)) := by
    obtain ⟨bT, _⟩ := FiniteTensor.invariantPositiveForm.{0, uF, max uF uV}
      (Fin B.length) (fun i => GeneralLinear (B.size i) F.Carrier)
      (fun i => (σ i : Type (max uF uV))) (fun i => (σ i).representation)
      (fun i => Classical.choice (hσ i))
    exact ⟨bT⟩
  have hs : IsSmooth (B.blockTensor (fun i => (σ i).representation)) :=
    FiniteTensor.isSmooth_external _ (fun i => (σ i).property)
  rw [T.normalizedProductInductionFunctor_obj B σ, T.normalizedProductInduced_eq]
  exact glNormalizedParabolicInductionUnitarity.{uF, max uF uV} p F T n hn B _
    (B.blockTensor (fun i => (σ i).representation)) hs ht

/-- Both normalized GL induction preservation statements, with independent
field and carrier universes and no additional hypotheses. -/
theorem glNormalizedInductionUnitarity :
    GLNormalizedInductionUnitarityStatement.{uF, uV} :=
  ⟨glNormalizedParabolicInductionUnitarity, glNormalizedProductInductionUnitarity⟩

end Langlands
