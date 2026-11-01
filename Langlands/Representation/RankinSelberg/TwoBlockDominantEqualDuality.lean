import Langlands.Representation.RankinSelberg.TwoBlockJacquetConvergenceStatement
import Langlands.Representation.RankinSelberg.TwoBlockDominantDualKernel
import Langlands.Representation.RankinSelberg.TwoBlockLowerFourierTransportProof
import Langlands.Representation.Induction.InverseTranspose
import Langlands.Representation.Twist.PullbackProof
import Langlands.HarmonicAnalysis.RectangularFourierCommutationProof

/-! # Actual duality at the equal-rank boundary -/

noncomputable section

namespace Langlands.HarmonicAnalysis

open MeasureTheory

section InverseCharacter

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [MeasurableSpace K] [BorelSpace K] [LocallyCompactSpace K] [T2Space K]
  [TotallyDisconnectedSpace K]
  (ψ : UnitaryAdditiveCharacter K) (μ : AdditiveHaarMeasure K)

omit [BorelSpace K] [LocallyCompactSpace K] [T2Space K]
  [TotallyDisconnectedSpace K] in
/-- Negating the character reflects the spectral argument of the actual integral. -/
theorem fourierIntegral_scale_neg_one (G : K → ℂ) (y : K) :
    fourierIntegral (ψ.scale (-1)) μ G y = fourierIntegral ψ μ G (-y) := by
  unfold fourierIntegral
  congr 1
  funext x
  change ψ.complex ((↑(-1 : Kˣ) : K) * (x * y)) * G x = _
  simp only [Units.val_neg, Units.val_one, mul_neg, neg_mul, one_mul]

/-- The same supplied Haar measure is self-dual for the inverse character. -/
theorem IsSelfDual.scale_neg_one (hsd : IsSelfDual ψ μ) :
    IsSelfDual (ψ.scale (-1)) μ := by
  intro f
  constructor
  · intro y
    have hi := ((hsd f).1 y).comp_neg
    change Integrable (fun x =>
      ψ.complex ((-x) * y) * fourierIntegral ψ μ f (-x)) μ.measure at hi
    change Integrable (fun x =>
      (ψ.scale (-1)).complex (x * y) * fourierIntegral (ψ.scale (-1)) μ f x) μ.measure
    simp_rw [fourierIntegral_scale_neg_one]
    change Integrable (fun x =>
      ψ.complex ((↑(-1 : Kˣ) : K) * (x * y)) * fourierIntegral ψ μ f (-x)) μ.measure
    simpa only [Units.val_neg, Units.val_one, neg_mul, one_mul] using hi
  · intro y
    change fourierIntegral (ψ.scale (-1)) μ
      (fun x => fourierIntegral (ψ.scale (-1)) μ f x) y = f (-y)
    simp_rw [fourierIntegral_scale_neg_one]
    rw [fourierIntegral_comp_neg]
    have hh := (hsd f).2 y
    change fourierIntegral ψ μ (fourierIntegral ψ μ f) y = f (-y) at hh
    simpa only [neg_neg] using hh

end InverseCharacter

end Langlands.HarmonicAnalysis

namespace Langlands.RankinSelberg.DominantRankTransport

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
  TwoBlockDominantRectangular TwoBlockLowerUnipotentQuotient

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance equalDualityTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance equalDualityValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance equalDualityLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance equalDualityT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance equalDualitySecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance equalDualityMeasurable : MeasurableSpace F.Carrier := borel _
local instance equalDualityBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance equalDualityDisconnected : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance

/-- The supplied self-dual measure, with its inverse-character certificate. -/
def negatedSelfDualHaar (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ) :
    LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData (ψ.scale (-1)) :=
  ⟨ν.val, ν.property.scale_neg_one ψ ν.val⟩

@[simp] theorem negatedSelfDualHaar_val (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ) :
    (negatedSelfDualHaar F ψ ν).val = ν.val := rfl

/-- Inverse transpose negates every complex determinant-power exponent. -/
theorem determinantComplexPower_inverseTranspose (n : ℕ) (s : ℂ) :
    (F.canonicalTopologicalData.determinantComplexPower n s).comp
        (inverseTranspose n F.Carrier).toMonoidHom =
      F.canonicalTopologicalData.determinantComplexPower n (-s) := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  simp only [MonoidHom.comp_apply,
    PadicField.TopologicalData.determinantComplexPower_apply]
  change ((F.canonicalTopologicalData.determinantNorm n
      (inverseTranspose n F.Carrier g) : NNReal) : ℂ) ^ s =
    ((F.canonicalTopologicalData.determinantNorm n g : NNReal) : ℂ) ^ (-s)
  simp only [
    PadicField.TopologicalData.determinantNorm_inverseTranspose,
    Units.val_inv_eq_inv_val, NNReal.coe_inv, Complex.ofReal_inv]
  rw [Complex.inv_cpow_ofReal_nonneg (NNReal.coe_nonneg _) s, Complex.cpow_neg]

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
  {W : Fin 2 → Type uW} [hadd : ∀ i, AddCommGroup (W i)]
  [hmod : ∀ i, Module ℂ (W i)]

local instance equalDualityReverseAdd : ∀ i : Fin 2, AddCommGroup (W i.rev) :=
  fun i => hadd i.rev
local instance equalDualityReverseModule : ∀ i : Fin 2, Module ℂ (W i.rev) :=
  fun i => hmod i.rev
local instance equalDualityGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
local instance equalDualityGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance equalDualityUnipotentMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance equalDualityUnipotentBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
local instance equalDualityQuotientMeasurable (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
local instance equalDualityQuotientBorel (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
local instance equalDualityLowerMeasurable :
    MeasurableSpace (TwoBlockLowerUnipotentQuotient.LowerQuotient h F.Carrier) := borel _
local instance equalDualityLowerBorel :
    BorelSpace (TwoBlockLowerUnipotentQuotient.LowerQuotient h F.Carrier) := ⟨rfl⟩
local instance equalDualityReverseLowerMeasurable :
    MeasurableSpace (TwoBlockLowerUnipotentQuotient.LowerQuotient (reverse_sum h) F.Carrier) :=
  borel _
local instance equalDualityReverseLowerBorel :
    BorelSpace (TwoBlockLowerUnipotentQuotient.LowerQuotient (reverse_sum h) F.Carrier) := ⟨rfl⟩

/-- Complete reversal and inverse transpose preserve the opposite-twist parameter. -/
theorem reversedDual_oppositeTwistBlocks
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
    (u : ℝ) :
    (fun i : Fin 2 => inverseTransposePullback (twoBlockOppositeTwistBlocks F m τ u i.rev)) =
      twoBlockOppositeTwistBlocks F (fun i => m i.rev)
        (fun i => inverseTransposePullback (τ i.rev)) u := by
  funext i
  unfold inverseTransposePullback twoBlockOppositeTwistBlocks
  rw [twist_comp, determinantComplexPower_inverseTranspose]
  have he : -(if i.rev = 0 then -(u : ℂ) else (u : ℂ)) =
      (if i = 0 then -(u : ℂ) else (u : ℂ)) := by
    fin_cases i <;> simp
  rw [he]

open TwoBlockJacquet TwoBlockLowerUnfolding TwoBlockLowerFourier

variable (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
  (hσ : ∀ i, IsSmooth (σ i))
  (ψ : UnitaryAdditiveCharacter F.Carrier)
  (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
  (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)

/-- The fixed section equivalence discharges the scalar-section premise in
the published Fourier comparison. -/
theorem equalLowerGroupIntegrand_reversedDual
    (f : Sections F h σ) (Wtest : WhittakerFunctions ψ t)
    (Φ Φhat : SchwartzBruhat (Fin (t + 1) → F.Carrier))
    (hpair : IsRowFourierPair ψ ν.val Φ Φhat)
    (g : GeneralLinear (t + 1) F.Carrier) :
    groupIntegrand (fun i => secondDualFunctional ψ (σ i.rev) (ell i.rev))
        (reversedDualSectionEquiv F h σ hσ f) (firstDualFunction ψ t Wtest)
        Φhat ν.val (weylLong (t + 1) F.Carrier * inverseTranspose (t + 1) F.Carrier g) =
      (F.canonicalTopologicalData.normalizedAbs (determinant g : F.Carrier) : ℂ) *
        groupIntegrand ell f Wtest Φ ν.val g := by
  rw [groupIntegrand_def, groupIntegrand_def,
    lowerDualTest_rotation h ψ Wtest,
    reversedDualSectionEquiv_scalar F h σ hσ ψ ell]
  have hinv := weylInverseTranspose_involutive (t + 1) F.Carrier g
  simp only [weylInverseTranspose_apply] at hinv
  rw [hinv, partialSection_fourier F h ψ ν.val ν.property Φ Φhat hpair]
  ring

/-- The pointwise comparison descends along the actual lower duality. -/
theorem equalLowerIntegrand_reversedDual
    (f : Sections F h σ) (Wtest : WhittakerFunctions ψ t)
    (Φ Φhat : SchwartzBruhat (Fin (t + 1) → F.Carrier))
    (hpair : IsRowFourierPair ψ ν.val Φ Φhat)
    (z : LowerQuotient h F.Carrier) :
    integrand (fun i => secondDualFunctional ψ (σ i.rev) (ell i.rev))
        (reversedDualSectionEquiv F h σ hσ f) (firstDualFunction ψ t Wtest)
        Φhat ν.val (lowerDuality F.Carrier h z) =
      (((F.canonicalTopologicalData.residueCardinality : ℝ) ^
        (-TwoBlockLowerUnipotentQuotient.determinantOrder F h z) : ℝ) : ℂ) *
        integrand ell f Wtest Φ ν.val z := by
  induction z using Quotient.inductionOn with
  | h g =>
    rw [lowerDuality_mk, integrand_mk_eq_groupIntegrand,
      integrand_mk_eq_groupIntegrand,
      equalLowerGroupIntegrand_reversedDual F h σ hσ ψ ell ν f Wtest Φ Φhat hpair g,
      TwoBlockLowerUnipotentQuotient.determinantOrder_mk,
      F.canonicalTopologicalData.normalizedAbs_of_ne_zero (determinant g).ne_zero]

/-- The actual equal-rank lower coefficient law, including integrability and
the raw-norm integral, for the supplied standard quotient measure. -/
def EqualLowerFourierCoefficientLaw
    (μN : Measure (LeftUnipotentQuotient t F.Carrier)) : Prop :=
  ∀ (f : Sections F h σ) (Wtest : WhittakerFunctions ψ t)
    (Φ Φhat : SchwartzBruhat (Fin (t + 1) → F.Carrier)),
    IsRowFourierPair ψ ν.val Φ Φhat → ∀ k : ℤ,
      let E := integrand ell f Wtest Φ ν.val
      let ED := integrand (fun i => secondDualFunctional ψ (σ i.rev) (ell i.rev))
        (reversedDualSectionEquiv F h σ hσ f) (firstDualFunction ψ t Wtest) Φhat ν.val
      let μL := lowerQuotientMeasure F.Carrier h μN
      let μD := lowerQuotientMeasure F.Carrier (reverse_sum h) μN
      (Integrable ED
          (μD.restrict (TwoBlockLowerUnipotentQuotient.determinantSlice F (reverse_sum h) (-k))) ↔
        Integrable E
          (μL.restrict (TwoBlockLowerUnipotentQuotient.determinantSlice F h k))) ∧
      (∫ z, ED z
          ∂μD.restrict (TwoBlockLowerUnipotentQuotient.determinantSlice F (reverse_sum h) (-k))) =
        (F.canonicalTopologicalData.residueCardinality : ℂ) ^ (-k) *
          (∫ z, E z
            ∂μL.restrict (TwoBlockLowerUnipotentQuotient.determinantSlice F h k)) ∧
      (∫ z, ‖ED z‖
          ∂μD.restrict (TwoBlockLowerUnipotentQuotient.determinantSlice F (reverse_sum h) (-k))) =
        (F.canonicalTopologicalData.residueCardinality : ℝ) ^ (-k) *
          (∫ z, ‖E z‖
            ∂μL.restrict (TwoBlockLowerUnipotentQuotient.determinantSlice F h k))

/-- The actual section equivalence and published supplied-measure transport
prove the coefficient law, with no scalar-section comparison premise. -/
theorem equalLowerFourierCoefficientLaw
    [hN : Measure.IsMulRightInvariant (unipotentHaar F.Carrier t)]
    (μN : Measure (LeftUnipotentQuotient t F.Carrier))
    (hμN : IsCompatible (upperUnipotent (t + 1) F.Carrier)
      (generalLinearHaar F.Carrier t) (unipotentHaar F.Carrier t) μN) :
    EqualLowerFourierCoefficientLaw F h σ hσ ψ ell ν μN := by
  intro f Wtest Φ Φhat hpair k
  dsimp only
  let E := integrand ell f Wtest Φ ν.val
  let ED := integrand (fun i => secondDualFunctional ψ (σ i.rev) (ell i.rev))
    (reversedDualSectionEquiv F h σ hσ f) (firstDualFunction ψ t Wtest) Φhat ν.val
  let μL := lowerQuotientMeasure F.Carrier h μN
  let μD := lowerQuotientMeasure F.Carrier (reverse_sum h) μN
  have hm := lowerDuality_measure_transport F h hN μN hμN
  have hDslice : MeasurePreserving (lowerDuality F.Carrier h)
      (μL.restrict (TwoBlockLowerUnipotentQuotient.determinantSlice F h k))
      (μD.restrict (TwoBlockLowerUnipotentQuotient.determinantSlice F (reverse_sum h) (-k))) :=
    ⟨(lowerDuality F.Carrier h).continuous.measurable, (hm.2.2 k).1⟩
  have hE : ∀ᵐ z ∂μL.restrict (TwoBlockLowerUnipotentQuotient.determinantSlice F h k),
      ED (lowerDuality F.Carrier h z) =
        (((F.canonicalTopologicalData.residueCardinality : ℝ) ^ (-k) : ℝ) : ℂ) * E z := by
    filter_upwards [ae_restrict_mem
      (TwoBlockLowerUnipotentQuotient.isClopen_determinantSlice F h k).1.measurableSet] with z hz
    have hk := (TwoBlockLowerUnipotentQuotient.mem_determinantSlice_iff_determinantOrder F h).mp hz
    simpa only [hk] using
      equalLowerIntegrand_reversedDual F h σ hσ ψ ell ν f Wtest Φ Φhat hpair z
  have hq : 0 < (F.canonicalTopologicalData.residueCardinality : ℝ) := by
    exact_mod_cast Nat.zero_lt_one.trans F.canonicalTopologicalData.residueCardinality_gt_one
  have hs := scalar_transport (lowerDuality F.Carrier h).toMeasurableEquiv
    hDslice E ED ((F.canonicalTopologicalData.residueCardinality : ℝ) ^ (-k))
    (zpow_pos hq _) hE
  simpa only [Complex.ofReal_zpow, Complex.ofReal_natCast] using hs

end Langlands.RankinSelberg.DominantRankTransport
