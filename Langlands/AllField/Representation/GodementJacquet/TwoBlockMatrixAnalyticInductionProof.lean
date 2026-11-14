import Langlands.Representation.GodementJacquet.TwoBlockMatrixAnalyticInductionProof
import Langlands.AllField.Representation.GodementJacquet.TwoBlockAnalyticReduction
import Langlands.AllField.Representation.GodementJacquet.TwoBlockReverseRealization
/-!
# Conditional two-block Godement–Jacquet analytic induction

The ordinary two-block analytic induction follows from the actual generator
inputs (forward finite product expansions and reverse realization) for the
canonical normalized induced representation; the reduction module then gives the
published conditional statement, including the transformed predicate.
-/

noncomputable section

namespace Langlands.AllField.GodementJacquet
open Langlands.GodementJacquet hiding TwoBlockMatrixAnalyticInductionStatement TwoBlockOrdinaryMatrixAnalyticInductionStatement compactInducedCoefficientKernel compactProductPairingKernel exists_compactInducedCoefficientFormula exists_compactProductCoefficientFormula exists_compactProductPairing_expansion inverseTransposeProductReversalEquiv iotaMatrixAnalyticAssertions_product_iff padicMatrixFourierPair_compact_left_invariant padicMatrixFourierPair_leftRight_invariant twoBlockMatrixAnalyticInduction twoBlockMatrixAnalyticInduction_of_ordinary twoBlockOrdinaryMatrixAnalyticInduction
open Langlands.AllField.GodementJacquet

open Langlands.HarmonicAnalysis hiding padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis

universe uF uV

/-- Ordinary two-block analytic induction for the canonical normalized induced
representation of two smooth admissible blocks. -/
theorem twoBlockOrdinaryMatrixAnalyticInduction :
    TwoBlockOrdinaryMatrixAnalyticInductionStatement.{uF,uV} := by
  intro F _ _ _ _
  let : MeasurableSpace F := borel _
  let : BorelSpace F := ⟨rfl⟩
  let : ∀ n : ℕ, MeasurableSpace (GeneralLinear (n + 1) F) := fun _ => borel _
  let : ∀ n : ℕ, BorelSpace (GeneralLinear (n + 1) F) := fun _ => ⟨rfl⟩
  intro t m h V hadd hmod σ ω _hω hσ hadm P hblock
  exact matrixAnalyticAssertions_twoBlock_of_generators _
    (⟨⟩ : LocalFieldData F).residueCardinality_gt_one _ _ _ m _ σ P hblock
    (Langlands.AllField.GodementJacquet.TwoBlock.twoBlock_matrixGeneratorInputs F h σ hσ hadm P hblock)

/-- **Conditional two-block Godement–Jacquet analytic induction.** -/
theorem twoBlockMatrixAnalyticInduction :
    TwoBlockMatrixAnalyticInductionStatement.{uF,uV} :=
  twoBlockMatrixAnalyticInduction_of_ordinary twoBlockOrdinaryMatrixAnalyticInduction

end Langlands.AllField.GodementJacquet
