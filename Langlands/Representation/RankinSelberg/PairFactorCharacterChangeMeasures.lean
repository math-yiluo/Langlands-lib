import Langlands.HarmonicAnalysis.CharacterTransport
import Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof
import Langlands.LocalFactor.Harmonic.DualityProof
import Langlands.LocalFactor.Abelian.Padic

/-!
# Self-dual measures for a scaled additive character

If `μ` is self-dual for `ψ` and multiplication by `a` scales `μ` by `|a|`, then
`|a|^(1/2) μ` is self-dual for `ψ^a(x) = ψ(ax)`. Over a p-adic field, with
uniqueness of self-dual measures, every measure self-dual for `ψ^a` is
`|a|^(1/2)` times every measure self-dual for `ψ`.
-/

noncomputable section

open MeasureTheory

namespace Langlands.HarmonicAnalysis

section Scaling

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [MeasurableSpace K] [BorelSpace K]
  (ψ : UnitaryAdditiveCharacter K) (μ : AdditiveHaarMeasure K)

omit [BorelSpace K] in
/-- Scaling the character by `a` scales the spectral argument of the integral. -/
theorem fourierIntegral_scale (a : Kˣ) (G : K → ℂ) (y : K) :
    fourierIntegral (ψ.scale a) μ G y = fourierIntegral ψ μ G ((a : K) * y) := by
  unfold fourierIntegral
  congr 1
  funext x
  change ψ.complex ((a : K) * (x * y)) * G x = ψ.complex (x * ((a : K) * y)) * G x
  rw [mul_left_comm]

/-- Scaling the measure by `c` scales the integral by `c`. -/
theorem fourierIntegral_scale_measure (c : NNReal) (hc : 0 < c) (G : K → ℂ) (y : K) :
    fourierIntegral ψ (μ.scale c hc) G y = ((c : ℝ) : ℂ) * fourierIntegral ψ μ G y := by
  unfold fourierIntegral
  rw [AdditiveHaarMeasure.scale_measure, integral_smul_nnreal_measure, NNReal.smul_def,
    Complex.real_smul]

/-- If multiplication by `a` pushes `μ` forward to `d • μ`, then integrals of
`h (a x)` are `d` times integrals of `h`. -/
theorem integral_comp_mul_left_of_map (a : Kˣ) (d : NNReal)
    (hmap : μ.measure.map (fun x => (a : K) * x) = d • μ.measure) (h : K → ℂ) :
    ∫ x, h ((a : K) * x) ∂μ.measure = ((d : ℝ) : ℂ) * ∫ x, h x ∂μ.measure := by
  have he : MeasurableEmbedding (fun x : K => (a : K) * x) :=
    (Homeomorph.mulLeft₀ (a : K) a.ne_zero).measurableEmbedding
  calc ∫ x, h ((a : K) * x) ∂μ.measure
      = ∫ y, h y ∂(μ.measure.map (fun x => (a : K) * x)) := (he.integral_map h).symm
    _ = _ := by rw [hmap, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

/-- Integrability of `h (a x)` under the same pushforward hypothesis. -/
theorem integrable_comp_mul_left_of_map (a : Kˣ) (d : NNReal)
    (hmap : μ.measure.map (fun x => (a : K) * x) = d • μ.measure) {h : K → ℂ}
    (hh : Integrable h μ.measure) :
    Integrable (fun x => h ((a : K) * x)) μ.measure := by
  have he : MeasurableEmbedding (fun x : K => (a : K) * x) :=
    (Homeomorph.mulLeft₀ (a : K) a.ne_zero).measurableEmbedding
  have h' : Integrable h (μ.measure.map (fun x => (a : K) * x)) := by
    rw [hmap]
    exact hh.smul_measure_nnreal
  exact (he.integrable_map_iff (μ := μ.measure)).mp h'

variable [LocallyCompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]

/-- If `μ` is self-dual for `ψ` and multiplication by `a` pushes `μ` forward
to `(c^2)⁻¹ • μ`, then `c • μ` is self-dual for `ψ^a`. -/
theorem IsSelfDual.scale_of_map {ψ : UnitaryAdditiveCharacter K} {μ : AdditiveHaarMeasure K}
    (hsd : IsSelfDual ψ μ) (a : Kˣ) (c : NNReal) (hc : 0 < c)
    (hmap : μ.measure.map (fun x => (a : K) * x) = (c ^ 2)⁻¹ • μ.measure) :
    IsSelfDual (ψ.scale a) (μ.scale c hc) := by
  have hFT : ∀ (f : SchwartzBruhat K) (x : K),
      fourierTransform (ψ.scale a) (μ.scale c hc) f x =
        ((c : ℝ) : ℂ) * fourierTransform ψ μ f ((a : K) * x) := by
    intro f x
    change fourierIntegral (ψ.scale a) (μ.scale c hc) f x = _
    rw [fourierIntegral_scale, fourierIntegral_scale_measure]
    rfl
  -- the integrand of the second transform, as a function of `a x`
  have hint : ∀ (f : SchwartzBruhat K) (y x : K),
      (ψ.scale a).complex (x * y) * fourierTransform (ψ.scale a) (μ.scale c hc) f x =
        ((c : ℝ) : ℂ) * (fun z => ψ.complex (z * y) * fourierTransform ψ μ f z) ((a : K) * x) := by
    intro f y x
    rw [hFT]
    change ψ.complex ((a : K) * (x * y)) * _ = _
    rw [show (a : K) * (x * y) = (a : K) * x * y by ring]
    ring
  intro f
  constructor
  · intro y
    simp_rw [hint f y]
    exact ((integrable_comp_mul_left_of_map μ a _ hmap ((hsd f).1 y)).const_mul _).smul_measure_nnreal
  · intro y
    have hsq : (((c ^ 2)⁻¹ : NNReal) : ℝ) * (c : ℝ) * (c : ℝ) = 1 := by
      have : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
      push_cast
      field_simp
    change fourierIntegral (ψ.scale a) (μ.scale c hc)
      (fun x => fourierTransform (ψ.scale a) (μ.scale c hc) f x) y = f (-y)
    rw [fourierIntegral_scale, fourierIntegral_scale_measure]
    unfold fourierIntegral
    simp_rw [hFT]
    have hre : ∀ x, ψ.complex (x * ((a : K) * y)) *
        (((c : ℝ) : ℂ) * fourierTransform ψ μ f ((a : K) * x)) =
          ((c : ℝ) : ℂ) * (fun z => ψ.complex (z * y) * fourierTransform ψ μ f z)
            ((a : K) * x) := by
      intro x
      simp only
      rw [show x * ((a : K) * y) = (a : K) * x * y by ring]
      ring
    simp_rw [hre]
    have hcomp := integral_comp_mul_left_of_map μ a _ hmap
      (fun z => ψ.complex (z * y) * fourierTransform ψ μ f z)
    rw [integral_const_mul, hcomp]
    have h2 := (hsd f).2 y
    change fourierIntegral ψ μ (fun x => fourierTransform ψ μ f x) y = f (-y) at h2
    unfold fourierIntegral at h2
    rw [h2]
    calc ((c : ℝ) : ℂ) * (((c : ℝ) : ℂ) * (((((c ^ 2)⁻¹ : NNReal) : ℝ) : ℂ) * f (-y))) =
        (((((c ^ 2)⁻¹ : NNReal) : ℝ) * (c : ℝ) * (c : ℝ) : ℝ) : ℂ) * f (-y) := by
          push_cast
          ring
      _ = f (-y) := by rw [hsq, Complex.ofReal_one, one_mul]

end Scaling

end Langlands.HarmonicAnalysis

namespace Langlands.LocalFactor.PadicAbelian

open HarmonicAnalysis

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance selfDualScaleTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance selfDualScaleValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance selfDualScaleLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance selfDualScaleT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance selfDualScaleMeasurable : MeasurableSpace F.Carrier := borel _
local instance selfDualScaleBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance selfDualScaleDisconnected : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance

/-- `|a|^(1/2)` for the residue-normalized absolute value. -/
def sqrtNormalizedAbs (a : F.Carrierˣ) : NNReal :=
  NNReal.sqrt (F.canonicalTopologicalData.normalizedAbsUnits a : NNReal)

theorem sqrtNormalizedAbs_pos (a : F.Carrierˣ) : 0 < sqrtNormalizedAbs F a :=
  NNReal.sqrt_pos.mpr (Units.ne_zero _).bot_lt

theorem sqrtNormalizedAbs_sq (a : F.Carrierˣ) :
    ((sqrtNormalizedAbs F a : ℝ)) ^ 2 = F.canonicalTopologicalData.normalizedAbs (a : F.Carrier) := by
  rw [sqrtNormalizedAbs, ← NNReal.coe_pow, NNReal.sq_sqrt]
  rfl

/-- A measure self-dual for `ψ`, scaled by `|a|^(1/2)`, is self-dual for `ψ^a`. -/
theorem isSelfDual_scale (ψ : UnitaryAdditiveCharacter F.Carrier) (a : F.Carrierˣ)
    (ν : SelfDualHaar F.canonicalTopologicalData ψ) :
    IsSelfDual (ψ.scale a) (ν.val.scale (sqrtNormalizedAbs F a) (sqrtNormalizedAbs_pos F a)) := by
  apply IsSelfDual.scale_of_map ν.property
  rw [padicScalarHaarScaling F F.canonicalTopologicalData ν.val.measure a, sqrtNormalizedAbs,
    NNReal.sq_sqrt]

/-- The measure self-dual for `ψ^a` is `|a|^(1/2)` times the one self-dual for `ψ`. -/
theorem SelfDualHaar.val_eq_scale (ψ : UnitaryAdditiveCharacter F.Carrier) (a : F.Carrierˣ)
    (ν : SelfDualHaar F.canonicalTopologicalData ψ)
    (ν' : SelfDualHaar F.canonicalTopologicalData (ψ.scale a)) :
    ν'.val = ν.val.scale (sqrtNormalizedAbs F a) (sqrtNormalizedAbs_pos F a) := by
  obtain ⟨htd, hd⟩ := LocalFactors.padicFourierDuality p F F.canonicalTopologicalData
  exact (hd (ψ.scale a).toAddChar (ψ.scale a).continuous_toFun (ψ.scale a).nontrivial).2.2.1
    ν'.val _ ν'.property (isSelfDual_scale F ψ a ν)

end Langlands.LocalFactor.PadicAbelian
