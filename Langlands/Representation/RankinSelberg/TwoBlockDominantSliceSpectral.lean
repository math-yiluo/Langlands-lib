import Langlands.Representation.RankinSelberg.TwoBlockDominantQuotientKernelData
import Langlands.Representation.RankinSelberg.UnequalRankBlockZeroIntegralLaws

/-!
# Spectral dependence of the actual dominant quotient kernel on each slice

The exact supplied lower measure and the integral of the raw kernel's norm
are retained. All integrability assertions below are equivalences.
-/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockDominantRectangular

open MeasureTheory GeneralLinear Whittaker HarmonicAnalysis TwoBlockJacquet
  TwoBlockLowerUnipotentQuotient TwoBlockLowerFixedSlice

universe uF uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance : MeasurableSpace F.Carrier := borel F.Carrier
local instance : BorelSpace F.Carrier := ⟨rfl⟩

variable {t r j k : ℕ} {m : Fin 2 → ℕ} {h : ∑ i, (m i+1) = t+1}
  {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
  {σ : ∀ i, Representation ℂ (GeneralLinear (m i+1) F.Carrier) (W i)}
  {ψ : UnitaryAdditiveCharacter F.Carrier}
  (ν : AdditiveHaarMeasure F.Carrier)
  (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
  (f : Sections F h σ) (Wtest : WhittakerFunctions ψ r)

/-- Changing the parameter changes only the actual determinant weight. -/
theorem kernel_spectral (hr : r=t+(j+k+1)) (s : ℂ)
    (g : GeneralLinear (t+1) F.Carrier)
    (x : Matrix (Fin (m 0+1)) (Fin k) F.Carrier)
    (y : Matrix (Fin j) (Fin (m 1+1)) F.Carrier) :
    kernel ell f Wtest hr s g x y =
      kernel ell f Wtest hr 0 g x y *
        determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g s := by
  unfold kernel
  rw [show s - ((j+k+1 : ℕ) : ℂ)/2 + (j : ℂ) =
      (0 - ((j+k+1 : ℕ) : ℂ)/2 + (j : ℂ)) + s by ring,
    determinantWeight_exponent_add, mul_assoc]

/-- The complex rectangle integral keeps its spectral weight outside. -/
theorem representativeKernel_spectral (hr : r=t+(j+k+1)) (s : ℂ)
    (g : GeneralLinear (t+1) F.Carrier) :
    representativeKernel ν ell f Wtest hr s g =
      representativeKernel ν ell f Wtest hr 0 g *
        determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g s := by
  simp only [representativeKernel]
  simp_rw [kernel_spectral ell f Wtest hr s]
  exact integral_mul_const _ _

/-- The real profile is the integral of the raw norm, with its own weight. -/
theorem representativeNormProfile_spectral (hr : r=t+(j+k+1)) (s : ℂ)
    (g : GeneralLinear (t+1) F.Carrier) :
    representativeNormProfile ν ell f Wtest hr s g =
      representativeNormProfile ν ell f Wtest hr 0 g *
        ‖determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g s‖ := by
  simp only [representativeNormProfile]
  simp_rw [kernel_spectral ell f Wtest hr s, norm_mul]
  exact integral_mul_const _ _

/-- Fiber integrability is unchanged by the nonzero spectral weight. -/
theorem fiberIntegrable_spectral_iff (hr : r=t+(j+k+1)) (s : ℂ)
    (g : GeneralLinear (t+1) F.Carrier) :
    FiberIntegrable ν ell f Wtest hr s g ↔
      FiberIntegrable ν ell f Wtest hr 0 g := by
  have hw : determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g s ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr
      ((normalizedAbsoluteValue F.canonicalTopologicalData).ne_zero g.det_ne_zero)))
  simp only [FiberIntegrable]
  simp_rw [kernel_spectral ell f Wtest hr s]
  exact integrable_mul_const_iff (IsUnit.mk0 _ hw) _

/-- Actual spectral dependence after descent, without a representative choice. -/
theorem quotientKernel_spectral (hr : r=t+(j+k+1)) (s : ℂ)
    (q : LowerQuotient h F.Carrier) :
    quotientKernel ν ell f Wtest hr s q =
      quotientKernel ν ell f Wtest hr 0 q *
        spectralPoint F.canonicalTopologicalData.residueCardinality s ^
          TwoBlockLowerUnipotentQuotient.determinantOrder F h q := by
  induction q using Quotient.inductionOn with
  | h g =>
    rw [quotientKernel_mk, quotientKernel_mk,
      TwoBlockLowerUnipotentQuotient.determinantOrder_mk]
    change representativeKernel ν ell f Wtest hr s g = _
    rw [representativeKernel_spectral, normalizedDeterminantWeight_eq_spectralPoint_zpow]
    rfl

theorem quotientNormProfile_spectral (hr : r=t+(j+k+1)) (s : ℂ)
    (q : LowerQuotient h F.Carrier) :
    quotientNormProfile ν ell f Wtest hr s q =
      quotientNormProfile ν ell f Wtest hr 0 q *
        ‖spectralPoint F.canonicalTopologicalData.residueCardinality s ^
          TwoBlockLowerUnipotentQuotient.determinantOrder F h q‖ := by
  induction q using Quotient.inductionOn with
  | h g =>
    rw [quotientNormProfile_mk, quotientNormProfile_mk,
      TwoBlockLowerUnipotentQuotient.determinantOrder_mk]
    change representativeNormProfile ν ell f Wtest hr s g = _
    rw [representativeNormProfile_spectral, normalizedDeterminantWeight_eq_spectralPoint_zpow]
    rfl

theorem quotientFiberIntegrable_spectral_iff (hr : r=t+(j+k+1)) (s : ℂ)
    (q : LowerQuotient h F.Carrier) :
    quotientFiberIntegrable ν ell f Wtest hr s q ↔
      quotientFiberIntegrable ν ell f Wtest hr 0 q := by
  induction q using Quotient.inductionOn with
  | h g => exact fiberIntegrable_spectral_iff ν ell f Wtest hr s g

section Slices

variable [MeasurableSpace (LeftUnipotentQuotient t F.Carrier)]
  [BorelSpace (LeftUnipotentQuotient t F.Carrier)]
  [MeasurableSpace (LowerQuotient h F.Carrier)]
  [BorelSpace (LowerQuotient h F.Carrier)]

variable (νN : Measure (LeftUnipotentQuotient t F.Carrier))

/-- The actual zero-parameter coefficient on a lower determinant slice,
with exactly the transported supplied standard quotient measure. -/
def kernelSliceCoefficient (hr : r=t+(j+k+1)) (d : ℤ) : ℂ :=
  ∫ q in TwoBlockLowerUnipotentQuotient.determinantSlice F h d,
    quotientKernel ν ell f Wtest hr 0 q ∂lowerMeasure F h νN

/-- The zero-parameter slice integral of the real integral of the raw norm. -/
def kernelNormProfileSliceCoefficient (hr : r=t+(j+k+1)) (d : ℤ) : ℝ :=
  ∫ q in TwoBlockLowerUnipotentQuotient.determinantSlice F h d,
    quotientNormProfile ν ell f Wtest hr 0 q ∂lowerMeasure F h νN

omit [MeasurableSpace (LeftUnipotentQuotient t F.Carrier)]
  [BorelSpace (LeftUnipotentQuotient t F.Carrier)]
  [MeasurableSpace (LowerQuotient h F.Carrier)]
  [BorelSpace (LowerQuotient h F.Carrier)] in
theorem quotientKernel_spectral_onSlice (hr : r=t+(j+k+1)) (s : ℂ)
    (d : ℤ) (q : LowerQuotient h F.Carrier)
    (hq : q ∈ TwoBlockLowerUnipotentQuotient.determinantSlice F h d) :
    quotientKernel ν ell f Wtest hr s q =
      quotientKernel ν ell f Wtest hr 0 q *
        spectralPoint F.canonicalTopologicalData.residueCardinality s ^ d := by
  rw [quotientKernel_spectral,
    (TwoBlockLowerUnipotentQuotient.mem_determinantSlice_iff_determinantOrder F h).mp hq]

omit [MeasurableSpace (LeftUnipotentQuotient t F.Carrier)]
  [BorelSpace (LeftUnipotentQuotient t F.Carrier)]
  [MeasurableSpace (LowerQuotient h F.Carrier)]
  [BorelSpace (LowerQuotient h F.Carrier)] in
theorem quotientNormProfile_spectral_onSlice (hr : r=t+(j+k+1)) (s : ℂ)
    (d : ℤ) (q : LowerQuotient h F.Carrier)
    (hq : q ∈ TwoBlockLowerUnipotentQuotient.determinantSlice F h d) :
    quotientNormProfile ν ell f Wtest hr s q =
      quotientNormProfile ν ell f Wtest hr 0 q *
        ‖spectralPoint F.canonicalTopologicalData.residueCardinality s ^ d‖ := by
  rw [quotientNormProfile_spectral,
    (TwoBlockLowerUnipotentQuotient.mem_determinantSlice_iff_determinantOrder F h).mp hq]

omit [BorelSpace (LeftUnipotentQuotient t F.Carrier)] in
/-- The total complex slice integral has the exact coefficient scaling.
This identity does not assert convergence. -/
theorem setIntegral_quotientKernel_spectral (hr : r=t+(j+k+1)) (s : ℂ) (d : ℤ) :
    (∫ q in TwoBlockLowerUnipotentQuotient.determinantSlice F h d,
      quotientKernel ν ell f Wtest hr s q ∂lowerMeasure F h νN) =
      kernelSliceCoefficient ν ell f Wtest νN hr d *
        spectralPoint F.canonicalTopologicalData.residueCardinality s ^ d := by
  rw [setIntegral_congr_fun
    (TwoBlockLowerUnipotentQuotient.measurableSet_determinantSlice F h d)
    (fun q hq => quotientKernel_spectral_onSlice ν ell f Wtest hr s d q hq),
    integral_mul_const]
  rfl

omit [BorelSpace (LeftUnipotentQuotient t F.Carrier)] in
/-- Norm is taken before the rectangle integration, and its real slice
integral has the corresponding norm multiplier. -/
theorem setIntegral_quotientNormProfile_spectral
    (hr : r=t+(j+k+1)) (s : ℂ) (d : ℤ) :
    (∫ q in TwoBlockLowerUnipotentQuotient.determinantSlice F h d,
      quotientNormProfile ν ell f Wtest hr s q ∂lowerMeasure F h νN) =
      kernelNormProfileSliceCoefficient ν ell f Wtest νN hr d *
        ‖spectralPoint F.canonicalTopologicalData.residueCardinality s ^ d‖ := by
  rw [setIntegral_congr_fun
    (TwoBlockLowerUnipotentQuotient.measurableSet_determinantSlice F h d)
    (fun q hq => quotientNormProfile_spectral_onSlice ν ell f Wtest hr s d q hq),
    integral_mul_const]
  rfl

omit [BorelSpace (LeftUnipotentQuotient t F.Carrier)] in
/-- Genuine outer integrability on a single slice is equivalent at `s` and zero. -/
theorem integrableOn_quotientKernel_spectral_iff
    (hr : r=t+(j+k+1)) (s : ℂ) (d : ℤ) :
    IntegrableOn (quotientKernel ν ell f Wtest hr s)
      (TwoBlockLowerUnipotentQuotient.determinantSlice F h d) (lowerMeasure F h νN) ↔
    IntegrableOn (quotientKernel ν ell f Wtest hr 0)
      (TwoBlockLowerUnipotentQuotient.determinantSlice F h d) (lowerMeasure F h νN) := by
  have hc : spectralPoint F.canonicalTopologicalData.residueCardinality s ^ d ≠ 0 :=
    zpow_ne_zero _ (spectralPoint_ne_zero_of_pos
      (Nat.zero_lt_one.trans F.canonicalTopologicalData.residueCardinality_gt_one) s)
  rw [integrableOn_congr_fun
    (fun q hq => quotientKernel_spectral_onSlice ν ell f Wtest hr s d q hq)
    (TwoBlockLowerUnipotentQuotient.measurableSet_determinantSlice F h d)]
  exact integrable_mul_const_iff (IsUnit.mk0 _ hc) _

omit [BorelSpace (LeftUnipotentQuotient t F.Carrier)] in
/-- Genuine outer integrability of the raw-norm profile has the same equivalence. -/
theorem integrableOn_quotientNormProfile_spectral_iff
    (hr : r=t+(j+k+1)) (s : ℂ) (d : ℤ) :
    IntegrableOn (quotientNormProfile ν ell f Wtest hr s)
      (TwoBlockLowerUnipotentQuotient.determinantSlice F h d) (lowerMeasure F h νN) ↔
    IntegrableOn (quotientNormProfile ν ell f Wtest hr 0)
      (TwoBlockLowerUnipotentQuotient.determinantSlice F h d) (lowerMeasure F h νN) := by
  have hc : spectralPoint F.canonicalTopologicalData.residueCardinality s ^ d ≠ 0 :=
    zpow_ne_zero _ (spectralPoint_ne_zero_of_pos
      (Nat.zero_lt_one.trans F.canonicalTopologicalData.residueCardinality_gt_one) s)
  rw [integrableOn_congr_fun
    (fun q hq => quotientNormProfile_spectral_onSlice ν ell f Wtest hr s d q hq)
    (TwoBlockLowerUnipotentQuotient.measurableSet_determinantSlice F h d)]
  exact integrable_mul_const_iff (IsUnit.mk0 _ (norm_ne_zero_iff.mpr hc)) _

omit [BorelSpace (LeftUnipotentQuotient t F.Carrier)]
  [BorelSpace (LowerQuotient h F.Carrier)] in
/-- The actual fiber condition is equivalent almost everywhere for the exact
restricted lower measure, independently of outer integrability. -/
theorem ae_quotientFiberIntegrable_spectral_iff
    (hr : r=t+(j+k+1)) (s : ℂ) (d : ℤ) :
    (∀ᵐ q ∂(lowerMeasure F h νN).restrict
      (TwoBlockLowerUnipotentQuotient.determinantSlice F h d),
      quotientFiberIntegrable ν ell f Wtest hr s q) ↔
    (∀ᵐ q ∂(lowerMeasure F h νN).restrict
      (TwoBlockLowerUnipotentQuotient.determinantSlice F h d),
      quotientFiberIntegrable ν ell f Wtest hr 0 q) :=
  Filter.eventually_congr (Filter.Eventually.of_forall
    (fun q => quotientFiberIntegrable_spectral_iff ν ell f Wtest hr s q))

/-- Package the three genuine convergence equivalences on one slice using
the existing absolute-input predicate and restriction of the supplied measure. -/
theorem kernelAbsoluteIntegrable_restrict_spectral_iff
    (hr : r=t+(j+k+1)) (s : ℂ) (d : ℤ) :
    KernelAbsoluteIntegrable ν ell f Wtest hr s
      (νN.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData t d)) ↔
    KernelAbsoluteIntegrable ν ell f Wtest hr 0
      (νN.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData t d)) := by
  simp only [kernelAbsoluteIntegrable_iff, KernelOuterIntegrable, OuterIntegrable,
    KernelNormProfileIntegrable, NormProfileIntegrable]
  have hmeasure :
      lowerMeasure F h
        (νN.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData t d)) =
      (lowerMeasure F h νN).restrict
        (TwoBlockLowerUnipotentQuotient.determinantSlice F h d) :=
    (lowerMeasure_restrict F h νN d).symm
  rw [hmeasure]
  exact and_congr
    (integrableOn_quotientKernel_spectral_iff ν ell f Wtest νN hr s d)
    (and_congr
      (integrableOn_quotientNormProfile_spectral_iff ν ell f Wtest νN hr s d)
      (ae_quotientFiberIntegrable_spectral_iff ν ell f Wtest νN hr s d))

end Slices

end Langlands.RankinSelberg.TwoBlockDominantRectangular
