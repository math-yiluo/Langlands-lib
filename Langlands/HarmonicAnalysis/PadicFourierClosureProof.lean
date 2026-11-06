import Langlands.LocalFactor.Harmonic.Statement
import Langlands.HarmonicAnalysis.PadicSelfDualMeasureExistsProof
import Langlands.HarmonicAnalysis.ScalarFourierClosureProof
import Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof

/-! Fourier closure for every supplied additive Haar measure on a p-adic field. -/

noncomputable section

open MeasureTheory

namespace Langlands.HarmonicAnalysis

universe u

/-- The plus-sign scalar Fourier transform preserves locally constant compactly
supported functions for every actual additive Haar measure and supplied topology. -/
theorem padicFourierClosure : LocalFactors.PadicFourierClosureStatement.{u} := by
  intro p _ F T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  let := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := T.fieldT2
  obtain ⟨htd, hexists⟩ := padicSelfDualMeasureExists F T
  let := htd
  intro ψ hψ hne μ hμ f hfl hfc
  let := hμ
  let χ : UnitaryAdditiveCharacter F.Carrier := ⟨ψ, hψ, hne⟩
  let ν : AdditiveHaarMeasure F.Carrier := ⟨μ, hμ, T.haarMeasure_regular μ⟩
  let φ : SchwartzBruhat F.Carrier := ⟨f, hfl, hfc⟩
  obtain ⟨σ, hσ⟩ := hexists χ
  obtain ⟨g, hg⟩ := scalarFourierClosed_of_compactAnnihilator χ ν
    (compactOpenAnnihilator F.Carrier χ σ hσ) φ
  have hplus (y : F.Carrier) :
      Fourier.fourierIntegral ψ⁻¹ μ f y = ∫ x, (ψ (x * y) : ℂ) * f x ∂μ := by
    simp only [Fourier.fourierIntegral_def, AddChar.inv_apply, neg_neg,
      Circle.smul_def, smul_eq_mul]
  have htransform : Fourier.fourierIntegral ψ⁻¹ μ f = (g : F.Carrier → ℂ) := by
    funext y
    exact (hplus y).trans (hg y).symm
  refine ⟨hfl.continuous.integrable_of_hasCompactSupport hfc, ?_, hplus, ?_, ?_, ?_⟩
  · intro y
    exact fourierIntegrand_integrable χ ν φ y
  · rw [htransform]
    exact g.locallyConstant
  · rw [htransform]
    exact g.hasCompactSupport
  · rw [htransform]
    exact g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport

end Langlands.HarmonicAnalysis
