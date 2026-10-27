import Langlands.Representation.Shahidi.JacquetIntegral
import Langlands.Representation.Shahidi.IntertwiningCovariance

/-! # Scalar Jacquet covariance under exchanged unipotent diagonal blocks -/

noncomputable section

namespace Langlands.Shahidi

open GeneralLinear HarmonicAnalysis MeasureTheory

universe uF uV

/-- The exchanged diagonal upper-unipotent blocks preserve rectangular Haar
measure and the Jacquet kernel. A scalar left-covariance law for the inducing
function therefore gives right covariance of its ordinary scalar Jacquet
integral on the integrable domain. -/
def JacquetDiagonalCovarianceStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.secondCountableTopology
    letI := T.fieldT2
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ψ : UnitaryAdditiveCharacter F.Carrier) (m n : ℕ) (ℓ : V →ₗ[ℂ] ℂ)
      (μ : Measure (Matrix (Fin (n + 1)) (Fin (m + 1)) F.Carrier)) [μ.IsAddHaarMeasure]
      (u₁ : upperUnipotent (m + 1) F.Carrier)
      (u₂ : upperUnipotent (n + 1) F.Carrier) (z : ℂ)
      (f : Langlands.GeneralLinear (m + 1 + (n + 1)) F.Carrier → V),
      (∀ g, ℓ (f (blockSum (u₁.val, u₂.val) * g)) = z * ℓ (f g)) →
      μ.map (rectangularConj u₂.val u₁.val) = μ ∧
      (∀ x, jacquetIntegrand m n ψ ℓ
          (fun g => f (g * swapRank (m + 1) (n + 1) F.Carrier
            (blockSum (u₂.val, u₁.val)))) x =
        z * jacquetIntegrand m n ψ ℓ f (rectangularConj u₂.val u₁.val x)) ∧
      (Integrable (jacquetIntegrand m n ψ ℓ f) μ →
        Integrable (jacquetIntegrand m n ψ ℓ
          (fun g => f (g * swapRank (m + 1) (n + 1) F.Carrier
            (blockSum (u₂.val, u₁.val))))) μ ∧
        (∫ x, jacquetIntegrand m n ψ ℓ
            (fun g => f (g * swapRank (m + 1) (n + 1) F.Carrier
              (blockSum (u₂.val, u₁.val)))) x ∂μ) =
          z * ∫ x, jacquetIntegrand m n ψ ℓ f x ∂μ)

end Langlands.Shahidi
