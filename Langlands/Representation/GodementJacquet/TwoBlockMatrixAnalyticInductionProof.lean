import Langlands.Representation.GodementJacquet.TwoBlockAnalyticReduction
import Langlands.Representation.GodementJacquet.TwoBlockAnalyticAssembly
import Langlands.Representation.GodementJacquet.TwoBlockReverseRealization

/-!
# Conditional two-block Godement–Jacquet analytic induction

The ordinary two-block analytic induction follows from the actual generator
inputs (forward finite product expansions and reverse realization) for the
canonical normalized induced representation; the reduction module then gives the
published conditional statement, including the transformed predicate.
-/

noncomputable section

namespace Langlands.GodementJacquet

open HarmonicAnalysis

universe uF uV

/-- Ordinary two-block analytic induction for the canonical normalized induced
representation of two smooth admissible blocks. -/
theorem twoBlockOrdinaryMatrixAnalyticInduction :
    TwoBlockOrdinaryMatrixAnalyticInductionStatement.{uF,uV} := by
  intro p hp F
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let : MeasurableSpace F.Carrier := borel _
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let : ∀ n : ℕ, MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := fun _ => borel _
  let : ∀ n : ℕ, BorelSpace (GeneralLinear (n + 1) F.Carrier) := fun _ => ⟨rfl⟩
  intro t m h V hadd hmod σ ω _hω hσ hadm P hblock
  exact matrixAnalyticAssertions_twoBlock_of_generators _
    F.canonicalTopologicalData.residueCardinality_gt_one _ _ _ m _ σ P hblock
    (TwoBlock.twoBlock_matrixGeneratorInputs F h σ hσ hadm P hblock)

/-- **Conditional two-block Godement–Jacquet analytic induction.** -/
theorem twoBlockMatrixAnalyticInduction :
    TwoBlockMatrixAnalyticInductionStatement.{uF,uV} :=
  twoBlockMatrixAnalyticInduction_of_ordinary twoBlockOrdinaryMatrixAnalyticInduction

end Langlands.GodementJacquet
