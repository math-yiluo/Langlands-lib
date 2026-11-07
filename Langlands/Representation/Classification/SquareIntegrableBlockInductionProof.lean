import Langlands.Representation.Classification.BlockTensorSquareIntegrableProof
import Langlands.Representation.Classification.LeviDiscreteSeriesTemperedProof
import Langlands.Representation.Classification.SquareIntegrableInductionIrreducibilityProof
import Langlands.Representation.Classification.TemperedBlockStatement
import Langlands.Representation.Classification.TemperedInductionPreservationProof
import Langlands.Representation.Induction.UnitaryProof
import Langlands.Representation.Smooth.Schur.Proof
import Langlands.Representation.Tensor.FiniteProperties

/-!
# Normalized induction of square-integrable GL blocks

Combine ordered-product irreducibility, preservation of invariant positive
forms, and analytic temperedness of normalized induction from the actual Levi.
-/

namespace Langlands.Classification

universe uF uV

/-- Pass from the analytic square-integrability of the blocks to temperedness
of their actual normalized product induction. -/
private theorem blockInduction_tempered
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (B : GeneralLinear.BlockShape n)
      (σ : ∀ i, SmoothRep.{0, uF, max uF uV} ℂ
        (GeneralLinear (B.size i) F.Carrier)),
      (∀ i, Representation.IsIrreducible (σ i).representation ∧
        T.IsSquareIntegrable (σ i).representation ∧
        IsUnitarizable (σ i).representation) →
      T.IsTempered ((T.normalizedProductInductionFunctor B).obj σ).representation := by
  let := T.topology
  intro n hn B σ hσ
  let := T.leviTopology B
  have := T.leviTopologicalGroup B
  have hirr : ∀ i, (σ i).representation.IsIrreducible := fun i => (hσ i).1
  have hadm : ∀ i, IsAdmissible (σ i).representation :=
    fun i => (hσ i).2.1.isAdmissible
  have hTensorIrreducible :
      (B.blockTensor (fun i => (σ i).representation)).IsIrreducible :=
    FiniteTensor.isIrreducible_external (fun i => (σ i).representation)
      (fun i φ => (admissibleSchur_scalarEndomorphism _ (hadm i) (hirr i) φ).exists)
  let := borel (B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier))
  have : BorelSpace (B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier)) := ⟨rfl⟩
  obtain ⟨μ, hμ⟩ := T.exists_isHaarMeasure_leviCentralQuotient B
  have := hμ
  have hTensorSquare :
      IsSquareIntegrableModCenter (B.blockTensor (fun i => (σ i).representation)) μ :=
    (glBlockTensorSquareIntegrable.{uF, max uF uV} p F T n hn B (fun i => σ i)
      (fun i => (σ i).representation) hirr hadm).mp (fun i => (hσ i).2.1) μ
  have hTensorTempered :
      IsTemperedModCenter (B.blockTensor (fun i => (σ i).representation)) μ :=
    glLeviDiscreteSeriesTempered.{uF, max uF uV}
      p F T n hn B μ _ _ hTensorIrreducible hTensorSquare
  exact glTemperedInductionPreservation.{uF, max uF uV}
    p F T n hn B μ _ _ hTensorIrreducible hTensorTempered

/-- Normalized induction of irreducible square-integrable unitarizable GL
blocks is irreducible, unitarizable and analytically tempered. -/
theorem squareIntegrableBlockInduction
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    SquareIntegrableBlockInduction.{uF, uV} F T := by
  let := T.topology
  intro n hn B σ hσ
  exact ⟨squareIntegrableBlockInductionIrreducibility.{uF, uV} F T n hn B σ hσ,
    (glNormalizedInductionUnitarity.{uF, uV}).2 p F T n hn B σ
      (fun i => (hσ i).2.2),
    blockInduction_tempered F T n hn B σ hσ⟩

end Langlands.Classification
