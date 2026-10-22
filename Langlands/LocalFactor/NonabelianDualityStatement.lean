import Langlands.LocalFactor.CommonClosureWeilDeligne
import Langlands.VirtualRepresentation.ExactDual

/-!
# Dual functional equations for actual local-constant systems

Deligne's formula uses the contragredient, the actual norm character, the inverse
additive character, and Fourier-dual Haar measures. Spectral values use the
existing unshifted Deligne convention.
-/

noncomputable section

universe uF uV

namespace Langlands.LocalFactor.NonabelianSystem

open CommonClosure CommonClosureSpectral VirtualRepresentation
open MeasureTheory

/-- Two supplied regular Haar measures are Fourier dual for the plus-sign
transform when its two successive integrals converge and give reflection.
No measure or inversion theorem is selected from an unproved proposition. -/
def FourierDualMeasures {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (E : Extension F) (ψ : AdditiveCharacter F E) (μ μ' : HaarMeasure F E) : Prop :=
  letI := (fieldData F E).topology
  letI := (fieldData F E).valuativeRel
  letI := (fieldData F E).localField
  letI : MeasurableSpace E.field := borel E.field
  letI : BorelSpace E.field := ⟨rfl⟩
  ∀ f : HarmonicAnalysis.SchwartzBruhat E.field,
    (∀ y : E.field, Integrable (fun x =>
      ψ.complex (x * y) * HarmonicAnalysis.fourierTransform ψ μ f x) μ'.measure) ∧
    ∀ y : E.field,
      HarmonicAnalysis.fourierIntegral ψ μ'
        (HarmonicAnalysis.fourierTransform ψ μ f) y = f (-y)

/-- Deligne 5.7.1 on the continuous exact virtual group, with the norm twist of
the actual contragredient and the inverse character `x ↦ ψ(-x)`. -/
def FixedHaarDualityStatement : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (e : ReciprocityFamily F) (ε : Assignment.{uF, uV} F),
    IsSystem F e ε →
    ∀ E : Extension F,
    letI := (fieldData F E).topology
    letI := (fieldData F E).valuativeRel
    letI := (fieldData F E).localField
    ∀ (ψ : AdditiveCharacter F E) (μ μ' : HaarMeasure F E),
      FourierDualMeasures F E ψ μ μ' →
      ∀ x : Virtual.{uF, uV} F E,
        ε E ψ μ x *
          ε E (ψ.scale (-1)) μ'
            (ExactGrothendieckGroup.continuousTwist
              (CommonClosureWeilDeligne.normCharacter F E)
              (ExactGrothendieckGroup.continuousDual x)) = 1

/-- The spectral version has complementary parameters `s` and `1-s`.
Both values are units, so no meromorphic evaluation domain is needed. -/
def SpectralDualityStatement : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (e : ReciprocityFamily F) (ε : Assignment.{uF, uV} F)
    (hε : IsSystem F e ε),
    ∀ E : Extension F,
    letI := (fieldData F E).topology
    letI := (fieldData F E).valuativeRel
    letI := (fieldData F E).localField
    ∀ (ψ : AdditiveCharacter F E) (μ μ' : HaarMeasure F E),
      FourierDualMeasures F E ψ μ μ' →
      ∀ (x : Virtual.{uF, uV} F E) (s : ℂ),
        conditionalDeligneValue F e ε hε E ψ μ x s *
          conditionalDeligneValue F e ε hε E (ψ.scale (-1)) μ'
            (ExactGrothendieckGroup.continuousDual x) (1 - s) = 1

/-- The ordinary and spectral dual functional equations. These are statement
targets, not proofs or additions to the imported system specification. -/
def DualFunctionalEquationStatement : Prop :=
  FixedHaarDualityStatement.{uF, uV} ∧ SpectralDualityStatement.{uF, uV}

end Langlands.LocalFactor.NonabelianSystem
