import Langlands.Representation.Whittaker.TwoBlockCellIntegrabilityStatement
import Langlands.AllField.Representation.Whittaker.TwoBlockOpenCell
/-! # Scalar Jacquet integrability on the actual two-block cell submodule -/

noncomputable section

namespace Langlands.AllField.Whittaker
open Langlands.Whittaker hiding TwoBlockCellJacquetIntegrabilityStatement TwoBlockInducedCarrier hasCompactSupport_twoBlockCellRestriction twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellRestriction twoBlockCellSubmodule twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction
open Langlands.AllField.Whittaker

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis

universe uF uV

/-- Every scalar Jacquet integrand of an actual compactly supported cell vector
is integrable for a Borel measure finite on compact sets, including Haar measure.
No topology or continuity of the linear functional on the tensor carrier is
assumed. -/
def TwoBlockCellJacquetIntegrabilityStatement : Prop :=
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
      (ℓ : PiTensorProduct ℂ (Shahidi.pairCarrier V₁ V₂) →ₗ[ℂ] ℂ)
      (μ : Measure (Matrix (Fin (b + 1)) (Fin (a + 1)) F))
      [IsFiniteMeasureOnCompacts μ]
      (f : twoBlockCellSubmodule F a b π₁ π₂),
      Integrable (Shahidi.jacquetIntegrand a b ψ ℓ (twoBlockEval F a b π₁ π₂ f.val)) μ

end Langlands.AllField.Whittaker
