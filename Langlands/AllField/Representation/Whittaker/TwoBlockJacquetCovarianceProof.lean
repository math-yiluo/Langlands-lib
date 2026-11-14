import Langlands.Representation.Whittaker.TwoBlockJacquetCovarianceProof
import Langlands.AllField.Representation.Shahidi.JacquetDiagonalProof
import Langlands.AllField.Representation.Whittaker.TwoBlockCellUnipotentStabilityProof
import Langlands.AllField.Representation.Whittaker.TwoBlockInducingCovarianceProof
import Langlands.AllField.Representation.Whittaker.TwoBlockJacquetCovarianceStatement
/-! # Full upper-unipotent covariance of the scalar two-block Jacquet integral -/

noncomputable section

namespace Langlands.AllField.Whittaker
open Langlands.Whittaker hiding TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier TwoBlockInducingWhittakerCovarianceStatement TwoBlockJacquetCovarianceStatement exchangedParabolic hasCompactSupport_twoBlockCellRestriction mul_upperUnipotent_mem_twoBlockCell swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockInducingWhittakerCovariance twoBlockJacquetCovariance twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker

open _root_.MeasureTheory
open Langlands.GeneralLinear
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis

universe uF uV

section Algebra



end Algebra

/-- Actual normalized inducing covariance, followed by radical and diagonal
changes of variables, gives full upper-unipotent scalar covariance. -/
theorem twoBlockJacquetCovariance : TwoBlockJacquetCovarianceStatement.{uF, uV} := by
  intro F _ _ _ _ a b V₁ V₂ _ _ _ _ π₁ π₂
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.secondCountableTopology
  let := T.fieldT2
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  let := T.generalLinearTopologicalGroup (a + 1 + (b + 1))
  dsimp only
  intro ψ ℓ₁ hℓ₁ ℓ₂ hℓ₂ μ _ f u hi
  obtain ⟨u₁, u₂, y, hu⟩ :=
    upperUnipotent_exchanged_factorization (Nat.succ_pos a) (Nat.succ_pos b) u
  let ℓ := Shahidi.pairFunctional ℓ₁ ℓ₂
  let z := (standardCharacter ψ a u₁ : ℂ) * (standardCharacter ψ b u₂ : ℂ)
  let d := Shahidi.swapRank (a + 1) (b + 1) F (blockSum (u₂.val, u₁.val))
  let fN := twoBlockInduced F a b π₁ π₂
    (Shahidi.intertwiningUnipotent (a + 1) (b + 1) F y) f
  have hNi : Integrable
      (Shahidi.jacquetIntegrand a b ψ ℓ (twoBlockEval F a b π₁ π₂ fN)) μ :=
    Shahidi.integrable_jacquetIntegrand_rightTranslate_intertwiningUnipotent
      ψ a b ℓ μ (twoBlockEval F a b π₁ π₂ f) y hi
  have hNe : (∫ x, Shahidi.jacquetIntegrand a b ψ ℓ
      (twoBlockEval F a b π₁ π₂ fN) x ∂μ) =
      (Shahidi.intertwiningCharacter a b ψ (Multiplicative.ofAdd y) : ℂ) *
        ∫ x, Shahidi.jacquetIntegrand a b ψ ℓ (twoBlockEval F a b π₁ π₂ f) x ∂μ :=
    Shahidi.integral_jacquetIntegrand_rightTranslate_intertwiningUnipotent
      ψ a b ℓ μ (twoBlockEval F a b π₁ π₂ f) y
  have hcov := twoBlockInducingWhittakerCovariance F ψ a b π₁ π₂
    ℓ₁ hℓ₁ ℓ₂ hℓ₂ fN u₁ u₂
  have hd := (Langlands.AllField.Shahidi.jacquetDiagonalCovariance F T _ ψ a b ℓ μ u₁ u₂ z
    (twoBlockEval F a b π₁ π₂ fN) hcov).2.2 hNi
  have hfull :
      (fun g => twoBlockEval F a b π₁ π₂ fN (g * d)) =
        twoBlockEval F a b π₁ π₂ (twoBlockInduced F a b π₁ π₂ u.val f) := by
    funext g
    change twoBlockEval F a b π₁ π₂ f
      ((g * d) * Shahidi.intertwiningUnipotent (a + 1) (b + 1) F y) =
        twoBlockEval F a b π₁ π₂ f (g * u.val)
    rw [mul_assoc, ← hu]
  change Integrable (Shahidi.jacquetIntegrand a b ψ ℓ
      (fun g => twoBlockEval F a b π₁ π₂ fN (g * d))) μ ∧
    (∫ x, Shahidi.jacquetIntegrand a b ψ ℓ
      (fun g => twoBlockEval F a b π₁ π₂ fN (g * d)) x ∂μ) = _ at hd
  rw [hfull] at hd
  refine ⟨hd.1, ?_⟩
  rw [hd.2, hNe, ← mul_assoc]
  congr 1
  let du : upperUnipotent (a + 1 + (b + 1)) F :=
    ⟨d, Shahidi.swapRank_mem_upperUnipotent _ _ _
      (blockSum_mem_upperUnipotent u₂ u₁)⟩
  let ny := Shahidi.intertwiningToUnipotent (a + 1) (b + 1) F
    (Multiplicative.ofAdd y)
  have hu' : u = du * ny := Subtype.ext hu
  rw [hu', map_mul, Units.val_mul]
  rw [standardCharacter_exchanged_blockSum]
  rfl

end Langlands.AllField.Whittaker
