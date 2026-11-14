import Langlands.Representation.Whittaker.TwoBlockJacquetCovarianceStatement
import Langlands.AllField.Group.GL.CompactOpenSupplement
import Langlands.AllField.Representation.Shahidi.IntertwiningCovariance
import Langlands.AllField.Representation.Whittaker.TwoBlockOpenCell
/-! # Full upper-unipotent covariance of the actual two-block scalar Jacquet integral -/

noncomputable section

namespace Langlands.AllField.Whittaker
open Langlands.Whittaker hiding TwoBlockInducedCarrier TwoBlockJacquetCovarianceStatement hasCompactSupport_twoBlockCellRestriction twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellRestriction twoBlockCellSubmodule twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction
open Langlands.AllField.Whittaker

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis

universe uF uV

/-- The scalar Jacquet integral from actual factor Whittaker functionals
transforms by the standard character under every upper-unipotent right
translation, whenever its initial integrand is integrable. -/
def TwoBlockJacquetCovarianceStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (a b : ℕ)
    {V₁ V₂ : Type uV} [AddCommGroup V₁] [Module ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂]
    (π₁ : Representation ℂ (Langlands.GeneralLinear (a + 1) F) V₁)
    (π₂ : Representation ℂ (Langlands.GeneralLinear (b + 1) F) V₂),
    let T := (⟨⟩ : LocalFieldData F)
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.secondCountableTopology
    letI := T.fieldT2
    letI := borel F
    letI : BorelSpace F := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F)
      (ℓ₁ : V₁ →ₗ[ℂ] ℂ), ℓ₁ ∈ glFunctionals ψ a π₁ →
      ∀ (ℓ₂ : V₂ →ₗ[ℂ] ℂ), ℓ₂ ∈ glFunctionals ψ b π₂ →
      ∀ (μ : Measure (Matrix (Fin (b + 1)) (Fin (a + 1)) F))
        [μ.IsAddHaarMeasure]
        (f : TwoBlockInducedCarrier F a b π₁ π₂)
        (u : GeneralLinear.upperUnipotent (a + 1 + (b + 1)) F),
        Integrable (Shahidi.jacquetIntegrand a b ψ (Shahidi.pairFunctional ℓ₁ ℓ₂)
          (twoBlockEval F a b π₁ π₂ f)) μ →
        Integrable (Shahidi.jacquetIntegrand a b ψ (Shahidi.pairFunctional ℓ₁ ℓ₂)
          (twoBlockEval F a b π₁ π₂ (twoBlockInduced F a b π₁ π₂ u.val f))) μ ∧
        (∫ x, Shahidi.jacquetIntegrand a b ψ (Shahidi.pairFunctional ℓ₁ ℓ₂)
          (twoBlockEval F a b π₁ π₂ (twoBlockInduced F a b π₁ π₂ u.val f)) x ∂μ) =
          (standardCharacter ψ (a + 1 + b) u : ℂ) *
            ∫ x, Shahidi.jacquetIntegrand a b ψ (Shahidi.pairFunctional ℓ₁ ℓ₂)
              (twoBlockEval F a b π₁ π₂ f) x ∂μ

end Langlands.AllField.Whittaker
