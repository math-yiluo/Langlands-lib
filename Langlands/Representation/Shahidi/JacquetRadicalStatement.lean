import Langlands.Representation.Shahidi.JacquetIntegral
import Mathlib.MeasureTheory.Group.Integral

/-! # Boundary kernel and exchanged-radical covariance of the scalar Jacquet integral -/

noncomputable section

namespace Langlands.Shahidi

open HarmonicAnalysis MeasureTheory

universe uF uV

/-- The exchanged-radical character is the character of its lower-left
rectangular corner, and the Jacquet kernel has the negative sign. -/
def IntertwiningJacquetBoundaryStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F]
    (ψ : UnitaryAdditiveCharacter F) (m n : ℕ)
    (x : Matrix (Fin (n + 1)) (Fin (m + 1)) F),
    (intertwiningCharacter m n ψ (Multiplicative.ofAdd x) : ℂ) =
      ψ.complex (x (Fin.last n) 0) ∧
    intertwiningJacquetKernel m n ψ x = ψ.complex (-(x (Fin.last n) 0))

/-- Right translation by an exchanged-radical element acts on the scalar
integrand by an additive coordinate translation and the positive character.
The ordinary integral has the same covariance on its integrable domain. -/
def IntertwiningJacquetTranslationStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    [MeasurableSpace F] [BorelSpace F]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ψ : UnitaryAdditiveCharacter F) (m n : ℕ) (ℓ : V →ₗ[ℂ] ℂ)
    (μ : Measure (Matrix (Fin (n + 1)) (Fin (m + 1)) F)) [μ.IsAddRightInvariant]
    (f : GeneralLinear (m + 1 + (n + 1)) F → V)
    (y : Matrix (Fin (n + 1)) (Fin (m + 1)) F),
    (∀ x,
      jacquetIntegrand m n ψ ℓ
          (fun g => f (g * intertwiningUnipotent (m + 1) (n + 1) F y)) x =
        (intertwiningCharacter m n ψ (Multiplicative.ofAdd y) : ℂ) *
          jacquetIntegrand m n ψ ℓ f (x + y)) ∧
    (Integrable (jacquetIntegrand m n ψ ℓ f) μ →
      Integrable (jacquetIntegrand m n ψ ℓ
        (fun g => f (g * intertwiningUnipotent (m + 1) (n + 1) F y))) μ ∧
      (∫ x, jacquetIntegrand m n ψ ℓ
          (fun g => f (g * intertwiningUnipotent (m + 1) (n + 1) F y)) x ∂μ) =
        (intertwiningCharacter m n ψ (Multiplicative.ofAdd y) : ℂ) *
          ∫ x, jacquetIntegrand m n ψ ℓ f x ∂μ)

/-- A focused scalar prerequisite for the two-block JPSS construction.
This proposition asserts covariance only for the exchanged rectangular radical. -/
def JacquetRadicalCovarianceStatement : Prop :=
  IntertwiningJacquetBoundaryStatement.{uF} ∧
    IntertwiningJacquetTranslationStatement.{uF, uV}

end Langlands.Shahidi
