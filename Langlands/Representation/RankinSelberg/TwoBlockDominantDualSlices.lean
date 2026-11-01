import Langlands.Representation.RankinSelberg.TwoBlockDominantDualKernel
import Langlands.Representation.RankinSelberg.TwoBlockDominantSliceSpectral
import Langlands.Representation.RankinSelberg.TwoBlockLowerFourierMeasure

/-!
# Actual dominant determinant slices under reversed duality

The matrix comparison remains an explicit premise. Every quotient measure is
the exact lower transport of the supplied compatible standard measure.
-/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockDominantRectangular

open MeasureTheory GeneralLinear Whittaker HarmonicAnalysis TwoBlockJacquet
  TwoBlockLowerUnipotentQuotient TwoBlockLowerFixedSlice QuotientIntegration

universe uF uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i+1) = t+1)
  {W : Fin 2 → Type uW} [hadd : ∀ i, AddCommGroup (W i)]
  [hmod : ∀ i, Module ℂ (W i)]
  (σ : ∀ i, Representation ℂ (GeneralLinear (m i+1) F.Carrier) (W i))

local instance dualSlicesTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance dualSlicesValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance dualSlicesLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance dualSlicesT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance dualSlicesMeasurable : MeasurableSpace F.Carrier := borel F.Carrier
local instance dualSlicesBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance dualSlicesAddCommGroup : ∀ i : Fin 2, AddCommGroup (W i.rev) :=
  fun i => hadd i.rev
local instance dualSlicesModule : ∀ i : Fin 2, Module ℂ (W i.rev) :=
  fun i => hmod i.rev
local instance dualSlicesGLTopologicalGroup :
    IsTopologicalGroup (GeneralLinear (t+1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearTopologicalGroup (t+1)
local instance dualSlicesGLMeasurable :
    MeasurableSpace (GeneralLinear (t+1) F.Carrier) := borel _
local instance dualSlicesGLBorel :
    BorelSpace (GeneralLinear (t+1) F.Carrier) := ⟨rfl⟩
local instance dualSlicesUnipotentMeasurable :
    MeasurableSpace (upperUnipotent (t+1) F.Carrier) := borel _
local instance dualSlicesUnipotentBorel :
    BorelSpace (upperUnipotent (t+1) F.Carrier) := ⟨rfl⟩
local instance dualSlicesStandardMeasurable :
    MeasurableSpace (LeftUnipotentQuotient t F.Carrier) := borel _
local instance dualSlicesStandardBorel :
    BorelSpace (LeftUnipotentQuotient t F.Carrier) := ⟨rfl⟩
local instance dualSlicesLowerMeasurable :
    MeasurableSpace (LowerQuotient h F.Carrier) := borel _
local instance dualSlicesLowerBorel :
    BorelSpace (LowerQuotient h F.Carrier) := ⟨rfl⟩
local instance dualSlicesLowerDualMeasurable :
    MeasurableSpace (LowerQuotient (reverse_sum h) F.Carrier) := borel _
local instance dualSlicesLowerDualBorel :
    BorelSpace (LowerQuotient (reverse_sum h) F.Carrier) := ⟨rfl⟩

variable (hσ : ∀ i, IsSmooth (σ i))
  (ψ : UnitaryAdditiveCharacter F.Carrier)
  (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
  {r j k : ℕ} (hr : r=t+(j+k+1))
  (f : Sections F h σ) (Wtest : WhittakerFunctions ψ r)
  (ν : AdditiveHaarMeasure F.Carrier)
  (νN : Measure (LeftUnipotentQuotient t F.Carrier))

/-- The actual zero-parameter slice coefficient of the fixed reversed dual
section and the prescribed Weyl-translated dual test. -/
def reversedDualSliceCoefficient (d : ℤ) : ℂ :=
  kernelSliceCoefficient ν
    (fun i => secondDualFunctional ψ (σ i.rev) (ell i.rev))
    (reversedDualSectionEquiv F h σ hσ f) (reversedDualTest hr ψ Wtest)
    νN (by omega : r=t+(k+j+1)) d

/-- The separate real slice integral of the dual raw-norm profile. -/
def reversedDualNormProfileSliceCoefficient (d : ℤ) : ℝ :=
  kernelNormProfileSliceCoefficient ν
    (fun i => secondDualFunctional ψ (σ i.rev) (ell i.rev))
    (reversedDualSectionEquiv F h σ hσ f) (reversedDualTest hr ψ Wtest)
    νN (by omega : r=t+(k+j+1)) d

variable (hN : Measure.IsMulRightInvariant (unipotentHaar F.Carrier t))
  (hνN : IsCompatible (upperUnipotent (t+1) F.Carrier)
    (generalLinearHaar F.Carrier t) (unipotentHaar F.Carrier t) νN)

include hN hνN in
omit σ hadd hmod hσ ψ ell hr f Wtest ν in
/-- The published exact measure law in the notation of the actual coefficients. -/
theorem lowerDuality_restrict_measurePreserving (d : ℤ) :
    MeasurePreserving (TwoBlockLowerFourier.lowerDuality F.Carrier h)
      ((lowerMeasure F h νN).restrict
        (TwoBlockLowerUnipotentQuotient.determinantSlice F h d))
      ((lowerMeasure F (reverse_sum h) νN).restrict
        (TwoBlockLowerUnipotentQuotient.determinantSlice F (reverse_sum h) (-d))) := by
  have hD := TwoBlockLowerFourier.lowerDuality_measure_transport F h hN νN hνN
  exact ⟨(TwoBlockLowerFourier.lowerDuality F.Carrier h).measurable,
    (hD.2.2 d).1⟩

variable (hMatrix : TwoBlockDominantDualMatrixStatement.{uF})

include hMatrix hN hνN

/-- Exact complex slice transport at complementary parameters, without any
convergence assumption or change of the supplied measure's scale. -/
theorem setIntegral_quotientKernel_reversedDual (s : ℂ) (d : ℤ) :
    (∫ q in TwoBlockLowerUnipotentQuotient.determinantSlice F (reverse_sum h) (-d),
      quotientKernel ν
        (fun i => secondDualFunctional ψ (σ i.rev) (ell i.rev))
        (reversedDualSectionEquiv F h σ hσ f) (reversedDualTest hr ψ Wtest)
        (by omega : r=t+(k+j+1)) (1-s) q
        ∂lowerMeasure F (reverse_sum h) νN) =
      ∫ q in TwoBlockLowerUnipotentQuotient.determinantSlice F h d,
        quotientKernel ν ell f Wtest hr s q ∂lowerMeasure F h νN := by
  have hD := lowerDuality_restrict_measurePreserving F h νN hN hνN d
  rw [← hD.integral_comp
    (TwoBlockLowerFourier.lowerDuality F.Carrier h).toMeasurableEquiv.measurableEmbedding]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun q =>
    quotientKernel_reversedDual F h σ hσ ψ ell hr hMatrix f Wtest ν s q

/-- The raw norm is integrated before either outer slice integral. -/
theorem setIntegral_quotientNormProfile_reversedDual (s : ℂ) (d : ℤ) :
    (∫ q in TwoBlockLowerUnipotentQuotient.determinantSlice F (reverse_sum h) (-d),
      quotientNormProfile ν
        (fun i => secondDualFunctional ψ (σ i.rev) (ell i.rev))
        (reversedDualSectionEquiv F h σ hσ f) (reversedDualTest hr ψ Wtest)
        (by omega : r=t+(k+j+1)) (1-s) q
        ∂lowerMeasure F (reverse_sum h) νN) =
      ∫ q in TwoBlockLowerUnipotentQuotient.determinantSlice F h d,
        quotientNormProfile ν ell f Wtest hr s q ∂lowerMeasure F h νN := by
  have hD := lowerDuality_restrict_measurePreserving F h νN hN hνN d
  rw [← hD.integral_comp
    (TwoBlockLowerFourier.lowerDuality F.Carrier h).toMeasurableEquiv.measurableEmbedding]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun q =>
    quotientNormProfile_reversedDual F h σ hσ ψ ell hr hMatrix f Wtest ν s q

/-- Genuine complex outer integrability is transported in both directions. -/
theorem integrableOn_quotientKernel_reversedDual_iff (s : ℂ) (d : ℤ) :
    IntegrableOn
      (quotientKernel ν
        (fun i => secondDualFunctional ψ (σ i.rev) (ell i.rev))
        (reversedDualSectionEquiv F h σ hσ f) (reversedDualTest hr ψ Wtest)
        (by omega : r=t+(k+j+1)) (1-s))
      (TwoBlockLowerUnipotentQuotient.determinantSlice F (reverse_sum h) (-d))
      (lowerMeasure F (reverse_sum h) νN) ↔
    IntegrableOn (quotientKernel ν ell f Wtest hr s)
      (TwoBlockLowerUnipotentQuotient.determinantSlice F h d)
      (lowerMeasure F h νN) := by
  have hD := lowerDuality_restrict_measurePreserving F h νN hN hνN d
  rw [IntegrableOn, IntegrableOn,
    ← hD.integrable_comp_emb
      (TwoBlockLowerFourier.lowerDuality F.Carrier h).toMeasurableEquiv.measurableEmbedding]
  have heq :
      (quotientKernel ν
        (fun i => secondDualFunctional ψ (σ i.rev) (ell i.rev))
        (reversedDualSectionEquiv F h σ hσ f) (reversedDualTest hr ψ Wtest)
        (by omega : r=t+(k+j+1)) (1-s)) ∘
          TwoBlockLowerFourier.lowerDuality F.Carrier h =
        quotientKernel ν ell f Wtest hr s := by
    funext q
    exact quotientKernel_reversedDual F h σ hσ ψ ell hr hMatrix f Wtest ν s q
  rw [heq]

/-- The separate real raw-norm profile has genuine outer integrability
equivalence for the same restricted measures. -/
theorem integrableOn_quotientNormProfile_reversedDual_iff (s : ℂ) (d : ℤ) :
    IntegrableOn
      (quotientNormProfile ν
        (fun i => secondDualFunctional ψ (σ i.rev) (ell i.rev))
        (reversedDualSectionEquiv F h σ hσ f) (reversedDualTest hr ψ Wtest)
        (by omega : r=t+(k+j+1)) (1-s))
      (TwoBlockLowerUnipotentQuotient.determinantSlice F (reverse_sum h) (-d))
      (lowerMeasure F (reverse_sum h) νN) ↔
    IntegrableOn (quotientNormProfile ν ell f Wtest hr s)
      (TwoBlockLowerUnipotentQuotient.determinantSlice F h d)
      (lowerMeasure F h νN) := by
  have hD := lowerDuality_restrict_measurePreserving F h νN hN hνN d
  rw [IntegrableOn, IntegrableOn,
    ← hD.integrable_comp_emb
      (TwoBlockLowerFourier.lowerDuality F.Carrier h).toMeasurableEquiv.measurableEmbedding]
  have heq :
      (quotientNormProfile ν
        (fun i => secondDualFunctional ψ (σ i.rev) (ell i.rev))
        (reversedDualSectionEquiv F h σ hσ f) (reversedDualTest hr ψ Wtest)
        (by omega : r=t+(k+j+1)) (1-s)) ∘
          TwoBlockLowerFourier.lowerDuality F.Carrier h =
        quotientNormProfile ν ell f Wtest hr s := by
    funext q
    exact quotientNormProfile_reversedDual F h σ hσ ψ ell hr hMatrix f Wtest ν s q
  rw [heq]

/-- The actual fiber predicate is transported almost everywhere, without a
measurability assumption on that predicate. -/
theorem ae_quotientFiberIntegrable_reversedDual_iff (s : ℂ) (d : ℤ) :
    (∀ᵐ q ∂(lowerMeasure F (reverse_sum h) νN).restrict
      (TwoBlockLowerUnipotentQuotient.determinantSlice F (reverse_sum h) (-d)),
      quotientFiberIntegrable ν
        (fun i => secondDualFunctional ψ (σ i.rev) (ell i.rev))
        (reversedDualSectionEquiv F h σ hσ f) (reversedDualTest hr ψ Wtest)
        (by omega : r=t+(k+j+1)) (1-s) q) ↔
    (∀ᵐ q ∂(lowerMeasure F h νN).restrict
      (TwoBlockLowerUnipotentQuotient.determinantSlice F h d),
      quotientFiberIntegrable ν ell f Wtest hr s q) := by
  have hD := lowerDuality_restrict_measurePreserving F h νN hN hνN d
  have hae :
      Filter.map (TwoBlockLowerFourier.lowerDuality F.Carrier h)
        (ae ((lowerMeasure F h νN).restrict
          (TwoBlockLowerUnipotentQuotient.determinantSlice F h d))) =
      ae ((lowerMeasure F (reverse_sum h) νN).restrict
        (TwoBlockLowerUnipotentQuotient.determinantSlice F (reverse_sum h) (-d))) := by
    calc
      _ = ae (Measure.map (TwoBlockLowerFourier.lowerDuality F.Carrier h)
          ((lowerMeasure F h νN).restrict
            (TwoBlockLowerUnipotentQuotient.determinantSlice F h d))) :=
        (TwoBlockLowerFourier.lowerDuality F.Carrier h).toMeasurableEquiv.map_ae _
      _ = _ := congrArg ae hD.map_eq
  rw [← hae, Filter.eventually_map]
  exact Filter.eventually_congr (Filter.Eventually.of_forall fun q =>
    quotientFiberIntegrable_reversedDual_iff F h σ hσ ψ ell hr hMatrix f Wtest ν s q)

/-- All three absolute-input conditions on the two complementary slices,
using restrictions of exactly the supplied standard measure. -/
theorem kernelAbsoluteIntegrable_restrict_reversedDual_iff (s : ℂ) (d : ℤ) :
    KernelAbsoluteIntegrable ν
      (fun i => secondDualFunctional ψ (σ i.rev) (ell i.rev))
      (reversedDualSectionEquiv F h σ hσ f) (reversedDualTest hr ψ Wtest)
      (by omega : r=t+(k+j+1)) (1-s)
      (νN.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData t (-d))) ↔
    KernelAbsoluteIntegrable ν ell f Wtest hr s
      (νN.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData t d)) := by
  simp only [kernelAbsoluteIntegrable_iff, KernelOuterIntegrable, OuterIntegrable,
    KernelNormProfileIntegrable, NormProfileIntegrable]
  have hmeasure :
      lowerMeasure F h
        (νN.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData t d)) =
      (lowerMeasure F h νN).restrict
        (TwoBlockLowerUnipotentQuotient.determinantSlice F h d) :=
    (lowerMeasure_restrict F h νN d).symm
  have hmeasureD :
      lowerMeasure F (reverse_sum h)
        (νN.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData t (-d))) =
      (lowerMeasure F (reverse_sum h) νN).restrict
        (TwoBlockLowerUnipotentQuotient.determinantSlice F (reverse_sum h) (-d)) :=
    (lowerMeasure_restrict F (reverse_sum h) νN (-d)).symm
  rw [hmeasure, hmeasureD]
  exact and_congr
    (integrableOn_quotientKernel_reversedDual_iff F h σ hσ ψ ell hr
      f Wtest ν νN hN hνN hMatrix s d)
    (and_congr
      (integrableOn_quotientNormProfile_reversedDual_iff F h σ hσ ψ ell hr
        f Wtest ν νN hN hνN hMatrix s d)
      (ae_quotientFiberIntegrable_reversedDual_iff F h σ hσ ψ ell hr
        f Wtest ν νN hN hνN hMatrix s d))

/-- The actual zero-parameter complex coefficients reflect with the exact
residue-cardinality multiplier. This is a total-integral identity. -/
theorem reversedDualSliceCoefficient_eq (d : ℤ) :
    reversedDualSliceCoefficient F h σ hσ ψ ell hr f Wtest ν νN d =
      (F.canonicalTopologicalData.residueCardinality : ℂ) ^ d *
        kernelSliceCoefficient ν ell f Wtest νN hr (-d) := by
  have heq := setIntegral_quotientKernel_reversedDual F h σ hσ ψ ell hr
    f Wtest ν νN hN hνN hMatrix 1 (-d)
  simp only [sub_self, neg_neg] at heq
  change (∫ q in TwoBlockLowerUnipotentQuotient.determinantSlice F (reverse_sum h) d,
    quotientKernel ν
      (fun i => secondDualFunctional ψ (σ i.rev) (ell i.rev))
      (reversedDualSectionEquiv F h σ hσ f) (reversedDualTest hr ψ Wtest)
      (by omega : r=t+(k+j+1)) 0 q ∂lowerMeasure F (reverse_sum h) νN) = _
  rw [heq, setIntegral_quotientKernel_spectral]
  simp only [spectralPoint, Complex.cpow_neg, Complex.cpow_one, inv_zpow,
    zpow_neg, inv_inv]
  exact mul_comm _ _

/-- The real raw-norm-profile coefficients have their own reflection law. -/
theorem reversedDualNormProfileSliceCoefficient_eq (d : ℤ) :
    reversedDualNormProfileSliceCoefficient F h σ hσ ψ ell hr f Wtest ν νN d =
      (F.canonicalTopologicalData.residueCardinality : ℝ) ^ d *
        kernelNormProfileSliceCoefficient ν ell f Wtest νN hr (-d) := by
  have heq := setIntegral_quotientNormProfile_reversedDual F h σ hσ ψ ell hr
    f Wtest ν νN hN hνN hMatrix 1 (-d)
  simp only [sub_self, neg_neg] at heq
  change (∫ q in TwoBlockLowerUnipotentQuotient.determinantSlice F (reverse_sum h) d,
    quotientNormProfile ν
      (fun i => secondDualFunctional ψ (σ i.rev) (ell i.rev))
      (reversedDualSectionEquiv F h σ hσ f) (reversedDualTest hr ψ Wtest)
      (by omega : r=t+(k+j+1)) 0 q ∂lowerMeasure F (reverse_sum h) νN) = _
  rw [heq, setIntegral_quotientNormProfile_spectral]
  simp only [spectralPoint, Complex.cpow_neg, Complex.cpow_one, inv_zpow,
    zpow_neg, inv_inv, norm_zpow, Complex.norm_natCast]
  exact mul_comm _ _

end Langlands.RankinSelberg.TwoBlockDominantRectangular
