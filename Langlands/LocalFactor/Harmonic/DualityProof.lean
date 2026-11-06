import Langlands.LocalFactor.Harmonic.Statement
import Langlands.HarmonicAnalysis.PadicSelfDualMeasureExistsProof
import Langlands.Representation.Hecke.TestFunction
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! Dual and self-dual Haar uniqueness by positive scalar comparison. -/

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace Langlands.HarmonicAnalysis

universe u

section ScalarComparison

variable {K : Type u} [Field K] [TopologicalSpace K] [MeasurableSpace K]

private theorem plusFourier_eq_integral (ψ : UnitaryAdditiveCharacter K)
    (μ : Measure K) (f : K → ℂ) (y : K) :
    Fourier.fourierIntegral ψ.toAddChar⁻¹ μ f y =
      ∫ x, ψ.complex (x * y) * f x ∂μ := by
  simp only [Fourier.fourierIntegral_def, AddChar.inv_apply, AddChar.map_neg_eq_inv,
    inv_inv, Circle.smul_def, UnitaryAdditiveCharacter.complex_apply, smul_eq_mul]

private theorem plusFourier_smul_measure (ψ : UnitaryAdditiveCharacter K)
    (μ : Measure K) (c : ℝ≥0) (f : K → ℂ) (y : K) :
    Fourier.fourierIntegral ψ.toAddChar⁻¹ (c • μ) f y =
      (c : ℂ) * Fourier.fourierIntegral ψ.toAddChar⁻¹ μ f y := by
  rw [plusFourier_eq_integral, plusFourier_eq_integral,
    integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

private theorem plusFourier_const_mul (ψ : UnitaryAdditiveCharacter K)
    (μ : Measure K) (c : ℂ) (f : K → ℂ) (y : K) :
    Fourier.fourierIntegral ψ.toAddChar⁻¹ μ (fun x => c * f x) y =
      c * Fourier.fourierIntegral ψ.toAddChar⁻¹ μ f y := by
  simp only [plusFourier_eq_integral, mul_left_comm (ψ.complex _) c,
    integral_const_mul]

private def RawDual (ψ : UnitaryAdditiveCharacter K) (μ ν : Measure K) : Prop :=
  ∀ (f : K → ℂ), IsLocallyConstant f → HasCompactSupport f →
    ∀ x, Fourier.fourierIntegral ψ.toAddChar⁻¹ ν
      (Fourier.fourierIntegral ψ.toAddChar⁻¹ μ f) x = f (-x)

variable [IsTopologicalRing K] [BorelSpace K]
  [LocallyCompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]

private theorem selfDual_raw (ψ : UnitaryAdditiveCharacter K)
    (σ : AdditiveHaarMeasure K) (hσ : IsSelfDual ψ σ) :
    RawDual ψ σ.measure σ.measure := by
  intro f hlc hc x
  have h := (hσ ⟨f, hlc, hc⟩).2 x
  change (∫ z, ψ.complex (z * x) *
    (∫ w, ψ.complex (w * z) * f w ∂σ.measure) ∂σ.measure) = f (-x) at h
  simpa only [plusFourier_eq_integral] using h

private theorem doubleFourier_scaled (ψ : UnitaryAdditiveCharacter K)
    (σ : AdditiveHaarMeasure K) (hσ : IsSelfDual ψ σ)
    (c d : ℝ≥0) (f : K → ℂ) (hlc : IsLocallyConstant f)
    (hc : HasCompactSupport f) (x : K) :
    Fourier.fourierIntegral ψ.toAddChar⁻¹ (d • σ.measure)
      (Fourier.fourierIntegral ψ.toAddChar⁻¹ (c • σ.measure) f) x =
      ((d * c : ℝ≥0) : ℂ) * f (-x) := by
  rw [plusFourier_smul_measure]
  have he : Fourier.fourierIntegral ψ.toAddChar⁻¹ (c • σ.measure) f =
      fun y => (c : ℂ) * Fourier.fourierIntegral ψ.toAddChar⁻¹ σ.measure f y :=
    funext (plusFourier_smul_measure ψ σ.measure c f)
  rw [he, plusFourier_const_mul, selfDual_raw ψ σ hσ f hlc hc]
  push_cast
  ring

private theorem rawDual_scaled_iff (ψ : UnitaryAdditiveCharacter K)
    (σ : AdditiveHaarMeasure K) (hσ : IsSelfDual ψ σ)
    (g : SchwartzBruhat K) (hg : g 0 = 1) (c d : ℝ≥0) :
    RawDual ψ (c • σ.measure) (d • σ.measure) ↔ d * c = 1 := by
  constructor
  · intro h
    have he := h g g.locallyConstant g.hasCompactSupport 0
    rw [doubleFourier_scaled ψ σ hσ c d g g.locallyConstant g.hasCompactSupport,
      neg_zero, hg, mul_one] at he
    exact_mod_cast he
  · intro h f hlc hc x
    rw [doubleFourier_scaled ψ σ hσ c d f hlc hc, h]
    simp

private theorem isSelfDual_iff_raw (ψ : UnitaryAdditiveCharacter K)
    (σ : AdditiveHaarMeasure K) (hσ : IsSelfDual ψ σ)
    (μ : AdditiveHaarMeasure K) :
    IsSelfDual ψ μ ↔ RawDual ψ μ.measure μ.measure := by
  constructor
  · exact selfDual_raw ψ μ
  · intro h f
    refine ⟨?_, ?_⟩
    · intro y
      let c : ℝ≥0 := μ.measure.addHaarScalarFactor σ.measure
      have hm : μ.measure = c • σ.measure :=
        Measure.isAddLeftInvariant_eq_smul_of_regular μ.measure σ.measure
      have he : fourierTransform ψ μ f = fun x => (c : ℂ) * fourierTransform ψ σ f x := by
        funext x
        change (∫ z, ψ.complex (z * x) * f z ∂μ.measure) = _
        rw [hm, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
        rfl
      have hint := ((hσ f).1 y).const_mul (c : ℂ)
      rw [hm]
      apply hint.smul_measure_nnreal.congr
      exact ae_of_all _ fun x => by
        rw [he]
        ring
    · intro x
      change (∫ z, ψ.complex (z * x) *
        (∫ w, ψ.complex (w * z) * f w ∂μ.measure) ∂μ.measure) = f (-x)
      simpa only [plusFourier_eq_integral]
        using h f f.locallyConstant f.hasCompactSupport x

private theorem selfDual_eq (ψ : UnitaryAdditiveCharacter K)
    (σ : AdditiveHaarMeasure K) (hσ : IsSelfDual ψ σ)
    (g : SchwartzBruhat K) (hg : g 0 = 1)
    (μ : AdditiveHaarMeasure K) (hμ : IsSelfDual ψ μ) : μ = σ := by
  let c : ℝ≥0 := μ.measure.addHaarScalarFactor σ.measure
  have hm : μ.measure = c • σ.measure :=
    Measure.isAddLeftInvariant_eq_smul_of_regular μ.measure σ.measure
  have hcc : c * c = 1 := (rawDual_scaled_iff ψ σ hσ g hg c c).1 (by
    rw [← hm]
    exact selfDual_raw ψ μ hμ)
  have hc : c = 1 := by
    exact (mul_self_inj (a := c) (b := 1) zero_le zero_le_one).1
      (by simpa only [one_mul] using hcc)
  have he : μ.measure = σ.measure := by simpa only [hc, one_smul] using hm
  cases μ
  cases σ
  cases he
  rfl

variable [SecondCountableTopology K]

private theorem rawDual_existsUnique (ψ : UnitaryAdditiveCharacter K)
    (σ : AdditiveHaarMeasure K) (hσ : IsSelfDual ψ σ)
    (g : SchwartzBruhat K) (hg : g 0 = 1)
    (μ : Measure K) [μ.IsAddHaarMeasure] :
    ∃! ν : Measure K, ν.IsAddHaarMeasure ∧ RawDual ψ μ ν := by
  let c : ℝ≥0 := μ.addHaarScalarFactor σ.measure
  have hc : c ≠ 0 :=
    (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ σ.measure).ne'
  have hm : μ = c • σ.measure :=
    Measure.isAddLeftInvariant_eq_smul μ σ.measure
  refine ⟨c⁻¹ • σ.measure,
    ⟨Measure.IsAddHaarMeasure.nnreal_smul σ.measure (inv_ne_zero hc), ?_⟩, ?_⟩
  · rw [hm]
    exact (rawDual_scaled_iff ψ σ hσ g hg c c⁻¹).2 (inv_mul_cancel₀ hc)
  · intro ν hν
    let := hν.1
    let d : ℝ≥0 := ν.addHaarScalarFactor σ.measure
    have hn : ν = d • σ.measure :=
      Measure.isAddLeftInvariant_eq_smul ν σ.measure
    have hdc : d * c = 1 := (rawDual_scaled_iff ψ σ hσ g hg c d).1 (by
      rw [← hm, ← hn]
      exact hν.2)
    have hd : d = c⁻¹ := by
      calc
        d = d * c * c⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hc, mul_one]
        _ = c⁻¹ := by rw [hdc, one_mul]
    simpa only [hd] using hn

private theorem rawDual_symm (ψ : UnitaryAdditiveCharacter K)
    (σ : AdditiveHaarMeasure K) (hσ : IsSelfDual ψ σ)
    (g : SchwartzBruhat K) (hg : g 0 = 1)
    (μ ν : Measure K) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (h : RawDual ψ μ ν) : RawDual ψ ν μ := by
  let c : ℝ≥0 := μ.addHaarScalarFactor σ.measure
  let d : ℝ≥0 := ν.addHaarScalarFactor σ.measure
  have hm : μ = c • σ.measure :=
    Measure.isAddLeftInvariant_eq_smul μ σ.measure
  have hn : ν = d • σ.measure :=
    Measure.isAddLeftInvariant_eq_smul ν σ.measure
  rw [hm, hn] at h ⊢
  apply (rawDual_scaled_iff ψ σ hσ g hg d c).2
  rw [mul_comm]
  exact (rawDual_scaled_iff ψ σ hσ g hg c d).1 h

end ScalarComparison

end Langlands.HarmonicAnalysis

namespace Langlands.LocalFactors

open HarmonicAnalysis

universe u

/-- Dual and self-dual Haar uniqueness and scalar Fourier inversion for every
supplied p-adic field topology. -/
theorem padicFourierDuality : PadicFourierDualityStatement.{u} := by
  intro p _ F T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  let := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  obtain ⟨htd, hex⟩ := padicSelfDualMeasureExists F T
  refine ⟨htd, ?_⟩
  let := htd
  let := T.secondCountableTopology
  intro ψ hψ hne
  let χ : UnitaryAdditiveCharacter F.Carrier := ⟨ψ, hψ, hne⟩
  obtain ⟨σ, hσ⟩ := hex χ
  let g : SchwartzBruhat F.Carrier :=
    Hecke.TestFunction.characteristic
      ⟨T.isCompact_integers.isClosed, T.isOpen_integers⟩ T.isCompact_integers
  have hg : g 0 = 1 := by
    change (T.Integers : Set F.Carrier).indicator (fun _ => (1 : ℂ)) 0 = 1
    exact Set.indicator_of_mem T.Integers.zero_mem _
  refine ⟨?_, ⟨σ, hσ⟩, ?_, ?_, ?_⟩
  · intro μ hμ
    let := hμ
    exact rawDual_existsUnique χ σ hσ g hg μ
  · intro μ ν hμ hν
    exact (selfDual_eq χ σ hσ g hg μ hμ).trans (selfDual_eq χ σ hσ g hg ν hν).symm
  · intro μ
    exact isSelfDual_iff_raw χ σ hσ μ
  · intro μ ν hμ hν h
    let := hμ
    let := hν
    exact rawDual_symm χ σ hσ g hg μ ν h

end Langlands.LocalFactors
