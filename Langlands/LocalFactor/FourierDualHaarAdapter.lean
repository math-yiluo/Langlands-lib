import Langlands.LocalFactor.NonabelianDualityStatement
import Langlands.LocalFactor.Harmonic.NormalizationProof
import Langlands.LocalFactor.Abelian.Definitions

/-! # Integer-ring volumes of the supplied Fourier-dual Haar measures -/

noncomputable section

universe uF

namespace Langlands.LocalFactor.NonabelianSystem

open CommonClosure MeasureTheory

/-- The actual convergence-bearing Fourier-dual condition forces the usual
integer-ring volume product. This is an internal consequence of Fourier
normalization, with no local-constant system or analytic epsilon law. -/
def FourierDualIntegerVolumeStatement : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (E : Extension F),
    letI := (fieldData F E).topology
    letI := (fieldData F E).valuativeRel
    letI := (fieldData F E).localField
    ∀ (ψ : AdditiveCharacter F E) (μ μ' : HaarMeasure F E),
      FourierDualMeasures F E ψ μ μ' →
      (fieldData F E).integerVolume μ * (fieldData F E).integerVolume μ' =
        ((fieldData F E).residueCardinality : ℝ) ^
          (-(fieldData F E).additiveConductor ψ)

/-- The project's plus-sign integral is Mathlib's transform for the inverse
additive character. This equality concerns the actual Bochner integrals. -/
private theorem fourierIntegral_eq_mathlib
    {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    [MeasurableSpace K] [BorelSpace K]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter K)
    (μ : HarmonicAnalysis.AdditiveHaarMeasure K) (f : K → ℂ) (y : K) :
    HarmonicAnalysis.fourierIntegral ψ μ f y =
      Fourier.fourierIntegral ψ.toAddChar⁻¹ μ.measure f y := by
  simp only [HarmonicAnalysis.fourierIntegral, Fourier.fourierIntegral_def,
    AddChar.inv_apply, neg_neg, Circle.smul_def, smul_eq_mul,
    HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply]

/-- The unchanged Fourier-dual predicate implies the published volume law. -/
theorem fourierDualIntegerVolume : FourierDualIntegerVolumeStatement.{uF} := by
  intro p hp F E ψ μ μ' hdual
  let := (fieldData F E).topology
  let := (fieldData F E).valuativeRel
  let := (fieldData F E).localField
  let : MeasurableSpace E.field := borel E.field
  let : BorelSpace E.field := ⟨rfl⟩
  have hraw : ∀ (f : E.field → ℂ), IsLocallyConstant f → HasCompactSupport f →
      ∀ x, Fourier.fourierIntegral ψ.toAddChar⁻¹ μ'.measure
        (Fourier.fourierIntegral ψ.toAddChar⁻¹ μ.measure f) x = f (-x) := by
    intro f hlc hc x
    have h := (hdual ⟨f, hlc, hc⟩).2 x
    change HarmonicAnalysis.fourierIntegral ψ μ'
      (fun y => HarmonicAnalysis.fourierIntegral ψ μ f y) x = f (-x) at h
    simpa only [fourierIntegral_eq_mathlib] using h
  have hn := (fieldData F E).isGreatest_fractionalIdeal_triviality ψ
  have hvol := ((LocalFactors.padicFourierNormalization p
    (E.asPadicField (p := p)) (fieldData F E) ψ.toAddChar
    ψ.continuous_toFun ψ.nontrivial _ hn).1
      μ.measure μ'.measure μ.isAddHaar μ'.isAddHaar).mp hraw
  have hO : Set.range (fun t : (fieldData F E).Integers => (t : E.field)) =
      ((fieldData F E).Integers : Set E.field) := by
    ext x
    simp
  simpa only [hO, PadicField.TopologicalData.integerVolume, Measure.real] using hvol

end Langlands.LocalFactor.NonabelianSystem
