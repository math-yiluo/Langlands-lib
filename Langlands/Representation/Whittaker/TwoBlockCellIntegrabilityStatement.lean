import Langlands.Representation.Whittaker.TwoBlockOpenCell
import Langlands.Representation.Shahidi.JacquetIntegral
import Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof

/-! # Scalar Jacquet integrability on the actual two-block cell submodule -/

noncomputable section

namespace Langlands.Whittaker

open HarmonicAnalysis MeasureTheory

universe uF uV

/-- Every scalar Jacquet integrand of an actual compactly supported cell vector
is integrable for a Borel measure finite on compact sets, including Haar measure.
No topology or continuity of the linear functional on the tensor carrier is
assumed. -/
def TwoBlockCellJacquetIntegrabilityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (a b : ℕ)
    {V₁ V₂ : Type uV} [AddCommGroup V₁] [Module ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂]
    (π₁ : Representation ℂ (Langlands.GeneralLinear (a + 1) F.Carrier) V₁)
    (π₂ : Representation ℂ (Langlands.GeneralLinear (b + 1) F.Carrier) V₂),
    let T := F.canonicalTopologicalData
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.secondCountableTopology
    letI := T.fieldT2
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
      (ℓ : PiTensorProduct ℂ (Shahidi.pairCarrier V₁ V₂) →ₗ[ℂ] ℂ)
      (μ : Measure (Matrix (Fin (b + 1)) (Fin (a + 1)) F.Carrier))
      [IsFiniteMeasureOnCompacts μ]
      (f : twoBlockCellSubmodule F a b π₁ π₂),
      Integrable (Shahidi.jacquetIntegrand a b ψ ℓ (twoBlockEval F a b π₁ π₂ f.val)) μ

end Langlands.Whittaker
