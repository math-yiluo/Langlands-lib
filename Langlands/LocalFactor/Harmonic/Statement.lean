import Langlands.LocalField.Normalization.Definitions
import Langlands.HarmonicAnalysis.Basic
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Fourier inversion and Haar normalization over p-adic fields

These are proposition targets, not proofs. All integrals are actual Mathlib
Bochner integrals for the Borel measurable space of the supplied topology.
`Fourier.fourierIntegral ψ⁻¹` uses the plus sign `ψ(x*y)`.

No local-constant system or self-dual measure is chosen from an unproved theorem.
The paired Markdown records the source correspondence and the correction to
the scalar-measure sentence following Tate (1979), equation (3.6.2).
-/

namespace Langlands.LocalFactors

open MeasureTheory

universe u

/-- The plus-sign Fourier transform preserves Schwartz--Bruhat functions.
The integrability conclusions exclude reliance on totalized divergent integrals. -/
def PadicFourierClosureStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData),
  letI := T.topology
  letI := borel F.Carrier
  ∀ (ψ : AddChar F.Carrier Circle), Continuous ψ → ψ ≠ 1 →
  ∀ (μ : Measure F.Carrier), μ.IsAddHaarMeasure →
  ∀ (f : F.Carrier → ℂ), IsLocallyConstant f → HasCompactSupport f →
    Integrable f μ ∧
    (∀ y, Integrable (fun x => (ψ (x * y) : ℂ) * f x) μ) ∧
    (∀ y, Fourier.fourierIntegral ψ⁻¹ μ f y =
      ∫ x, (ψ (x * y) : ℂ) * f x ∂μ) ∧
    IsLocallyConstant (Fourier.fourierIntegral ψ⁻¹ μ f) ∧
    HasCompactSupport (Fourier.fourierIntegral ψ⁻¹ μ f) ∧
    Integrable (Fourier.fourierIntegral ψ⁻¹ μ f) μ

/-- Existence and uniqueness of dual Haar measure for every fixed Haar measure,
and of self-dual Haar measure. Inversion is a conclusion in both clauses. -/
def PadicFourierDualityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData),
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  letI := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  letI := borel F.Carrier
  letI : BorelSpace F.Carrier := ⟨rfl⟩
  ∃ htd : TotallyDisconnectedSpace F.Carrier,
  letI := htd
  ∀ (ψ : AddChar F.Carrier Circle) (hψ : Continuous ψ) (hne : ψ ≠ 1),
  let χ : HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier := ⟨ψ, hψ, hne⟩
  let dual := fun (μ ν : Measure F.Carrier) =>
    ∀ (f : F.Carrier → ℂ), IsLocallyConstant f → HasCompactSupport f →
    ∀ x, Fourier.fourierIntegral ψ⁻¹ ν
      (Fourier.fourierIntegral ψ⁻¹ μ f) x = f (-x)
  (∀ (μ : Measure F.Carrier), μ.IsAddHaarMeasure →
    ∃! ν : Measure F.Carrier, ν.IsAddHaarMeasure ∧ dual μ ν) ∧
  HarmonicAnalysis.SelfDualMeasureExists χ ∧
  (∀ μ ν : HarmonicAnalysis.AdditiveHaarMeasure F.Carrier,
    HarmonicAnalysis.IsSelfDual χ μ → HarmonicAnalysis.IsSelfDual χ ν → μ = ν) ∧
  (∀ μ : HarmonicAnalysis.AdditiveHaarMeasure F.Carrier,
    HarmonicAnalysis.IsSelfDual χ μ ↔ dual μ.measure μ.measure) ∧
  (∀ (μ ν : Measure F.Carrier), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure →
    dual μ ν → dual ν μ)

/-- Scalar changes of Haar measure, additive character, and the argument of
a Schwartz--Bruhat function, with the actual residue-normalized absolute value. -/
def PadicFourierScalingStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData),
  letI := T.topology
  letI := borel F.Carrier
  ∀ (ψ : AddChar F.Carrier Circle), Continuous ψ → ψ ≠ 1 →
  ∀ (μ : Measure F.Carrier), μ.IsAddHaarMeasure →
  (∀ (a : F.Carrierˣ) (s : Set F.Carrier), MeasurableSet s →
    μ ((fun x => (a : F.Carrier) * x) '' s) =
      ENNReal.ofReal (T.normalizedAbs (a : F.Carrier)) * μ s) ∧
  (∀ (f : F.Carrier → ℂ), IsLocallyConstant f → HasCompactSupport f →
    (∀ (c : NNReal), c ≠ 0 → ∀ y,
      Fourier.fourierIntegral ψ⁻¹ (c • μ) f y =
        (c : ℂ) * Fourier.fourierIntegral ψ⁻¹ μ f y) ∧
    (∀ (a : F.Carrierˣ) (y : F.Carrier),
      Fourier.fourierIntegral (ψ.mulShift (a : F.Carrier))⁻¹ μ f y =
        Fourier.fourierIntegral ψ⁻¹ μ f ((a : F.Carrier) * y)) ∧
    (∀ (a : F.Carrierˣ) (y : F.Carrier),
      Fourier.fourierIntegral ψ⁻¹ μ (fun x => f ((a : F.Carrier) * x)) y =
        ((T.normalizedAbs (a : F.Carrier))⁻¹ : ℝ) *
          Fourier.fourierIntegral ψ⁻¹ μ f ((a⁻¹ : F.Carrierˣ) * y)))

/-- The additive conductor exists as the greatest triviality exponent on
the actual fractional integer ideals, and changes by `ord(a)` under `ψ(a*x)`. -/
def PadicAdditiveConductorStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData),
  letI := T.topology
  ∀ (ψ : AddChar F.Carrier Circle), Continuous ψ → ψ ≠ 1 →
  let conductor := fun (χ : AddChar F.Carrier Circle) (n : ℤ) =>
    IsGreatest {m : ℤ | ∀ t : T.Integers,
      χ (T.uniformizer ^ (-m) * (t : F.Carrier)) = 1} n
  (∃! n : ℤ, conductor ψ n) ∧
  (∀ (n : ℤ), conductor ψ n → ∀ a : F.Carrierˣ,
    conductor (ψ.mulShift (a : F.Carrier)) (n + T.ord (a : F.Carrier))) ∧
  (∀ (n : ℤ), conductor ψ n → ∀ y : F.Carrier,
    (∀ t : T.Integers, ψ ((t : F.Carrier) * y) = 1) ↔
      ∃ t : T.Integers, y = T.uniformizer ^ (-n) * (t : F.Carrier))

/-- The normalization of dual and self-dual measure, the integer-ring Fourier
formula, and the corrected fixed-Haar ratio. The conductor and self-duality
conditions here are concrete predicates, with existence asserted above. -/
def PadicFourierNormalizationStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData),
  letI := T.topology
  letI := borel F.Carrier
  ∀ (ψ : AddChar F.Carrier Circle), Continuous ψ → ψ ≠ 1 →
  let O : Set F.Carrier := Set.range (fun t : T.Integers => (t : F.Carrier))
  let dual := fun (χ : AddChar F.Carrier Circle) (μ ν : Measure F.Carrier) =>
    ∀ (f : F.Carrier → ℂ), IsLocallyConstant f → HasCompactSupport f →
    ∀ x, Fourier.fourierIntegral χ⁻¹ ν
      (Fourier.fourierIntegral χ⁻¹ μ f) x = f (-x)
  ∀ (n : ℤ), IsGreatest {m : ℤ | ∀ t : T.Integers,
    ψ (T.uniformizer ^ (-m) * (t : F.Carrier)) = 1} n →
  (∀ (μ ν : Measure F.Carrier), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure →
    (dual ψ μ ν ↔ (μ O).toReal * (ν O).toReal =
      (T.residueCardinality : ℝ) ^ (-n))) ∧
  (∀ (μ : Measure F.Carrier), μ.IsAddHaarMeasure →
    (dual ψ μ μ ↔ μ O =
      ENNReal.ofReal ((T.residueCardinality : ℝ) ^ (-(n : ℝ) / 2)))) ∧
  (∀ (μ : Measure F.Carrier), μ.IsAddHaarMeasure → ∀ y : F.Carrier,
    Fourier.fourierIntegral ψ⁻¹ μ (O.indicator (fun _ => (1 : ℂ))) y =
      (μ O).toReal * O.indicator (fun _ => (1 : ℂ)) (T.uniformizer ^ n * y)) ∧
  (∀ (μ σ : Measure F.Carrier), μ.IsAddHaarMeasure → σ.IsAddHaarMeasure →
    dual ψ σ σ →
    μ = ENNReal.ofReal
      ((T.residueCardinality : ℝ) ^ ((n : ℝ) / 2) * (μ O).toReal) • σ) ∧
  (∀ (μ : Measure F.Carrier), μ.IsAddHaarMeasure → dual ψ μ μ →
    ∀ a : F.Carrierˣ,
    dual (ψ.mulShift (a : F.Carrier))
      (ENNReal.ofReal (Real.sqrt (T.normalizedAbs (a : F.Carrier))) • μ)
      (ENNReal.ofReal (Real.sqrt (T.normalizedAbs (a : F.Carrier))) • μ))

/-- The whole local Fourier and Haar-normalization theorem family.
This is a proposition definition, with no proof or assumed solution. -/
def PadicHarmonicAnalysisStatement : Prop :=
  PadicFourierClosureStatement.{u} ∧
  PadicFourierDualityStatement.{u} ∧
  PadicFourierScalingStatement.{u} ∧
  PadicAdditiveConductorStatement.{u} ∧
  PadicFourierNormalizationStatement.{u}

end Langlands.LocalFactors
