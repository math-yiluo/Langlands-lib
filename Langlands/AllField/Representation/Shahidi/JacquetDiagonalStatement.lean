import Langlands.Representation.Shahidi.JacquetDiagonalStatement
import Langlands.AllField.Representation.Shahidi.IntertwiningCovariance
/-! # Scalar Jacquet covariance under exchanged unipotent diagonal blocks -/

noncomputable section

namespace Langlands.AllField.Shahidi
open Langlands.Shahidi hiding JacquetDiagonalCovarianceStatement map_rectangularConj_padic
open Langlands.AllField.Shahidi

open _root_.MeasureTheory
open Langlands.GeneralLinear
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis

universe uF uV

/-- The exchanged diagonal upper-unipotent blocks preserve rectangular Haar
measure and the Jacquet kernel. A scalar left-covariance law for the inducing
function therefore gives right covariance of its ordinary scalar Jacquet
integral on the integrable domain. -/
def JacquetDiagonalCovarianceStatement : Prop :=
  ∀ (F : Type uF) [Field F] (T : LocalFieldData F),
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.secondCountableTopology
    letI := T.fieldT2
    letI := borel F
    letI : BorelSpace F := ⟨rfl⟩
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ψ : UnitaryAdditiveCharacter F) (m n : ℕ) (ℓ : V →ₗ[ℂ] ℂ)
      (μ : Measure (Matrix (Fin (n + 1)) (Fin (m + 1)) F)) [μ.IsAddHaarMeasure]
      (u₁ : upperUnipotent (m + 1) F)
      (u₂ : upperUnipotent (n + 1) F) (z : ℂ)
      (f : Langlands.GeneralLinear (m + 1 + (n + 1)) F → V),
      (∀ g, ℓ (f (blockSum (u₁.val, u₂.val) * g)) = z * ℓ (f g)) →
      μ.map (rectangularConj u₂.val u₁.val) = μ ∧
      (∀ x, jacquetIntegrand m n ψ ℓ
          (fun g => f (g * swapRank (m + 1) (n + 1) F
            (blockSum (u₂.val, u₁.val)))) x =
        z * jacquetIntegrand m n ψ ℓ f (rectangularConj u₂.val u₁.val x)) ∧
      (Integrable (jacquetIntegrand m n ψ ℓ f) μ →
        Integrable (jacquetIntegrand m n ψ ℓ
          (fun g => f (g * swapRank (m + 1) (n + 1) F
            (blockSum (u₂.val, u₁.val))))) μ ∧
        (∫ x, jacquetIntegrand m n ψ ℓ
            (fun g => f (g * swapRank (m + 1) (n + 1) F
              (blockSum (u₂.val, u₁.val)))) x ∂μ) =
          z * ∫ x, jacquetIntegrand m n ψ ℓ f x ∂μ)

end Langlands.AllField.Shahidi
