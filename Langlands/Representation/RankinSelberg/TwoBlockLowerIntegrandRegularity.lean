import Langlands.Representation.RankinSelberg.TwoBlockLowerUnfoldingIntegrandData
import Langlands.HarmonicAnalysis.RowTestSmoothProof
import Langlands.Representation.Hecke.ActionIntegrand

/-! Local constancy and measurability of the actual Section 4.7 lower integrand. -/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockLowerUnfolding

open GeneralLinear TwoBlockJacquet TwoBlockLowerUnipotentQuotient
  QuotientIntegration Whittaker HarmonicAnalysis HarmonicAnalysis.TwoBlockRowPartialFourier

universe uF uV uW

section PartialSection

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
variable [MeasurableSpace F.Carrier]
variable (ψ : letI := F.canonicalTopologicalData.topology
  UnitaryAdditiveCharacter F.Carrier)
variable (μ : letI := F.canonicalTopologicalData.topology; AdditiveHaarMeasure F.Carrier)
variable (Φ : letI := F.canonicalTopologicalData.topology
  SchwartzBruhat (Fin (t + 1) → F.Carrier))

/-- Local constancy of the complete row-translate family passes through the fixed
first-block Fourier integral, for the supplied additive Haar measure. -/
theorem partialSection_locallyConstant :
    let := F.canonicalTopologicalData.topology
    IsLocallyConstant (partialSection h ψ μ Φ) := by
  let := F.canonicalTopologicalData.topology
  let := isTopologicalRing_carrier F
  have hΦ := (rowTranslate_locallyConstant Φ).comp
    (fun Ψ : (Fin (t + 1) → F.Carrier) → ℂ =>
      ∫ w, ψ.complex (w 0) *
        Ψ (join (succBlockEquiv h) w (eta (m 1))) ∂rowMeasure μ (m 0 + 1))
  simpa only [Function.comp_def, ← partialSection_apply] using hΦ

end PartialSection

section Sections

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable {t : ℕ} {m : Fin 2 → ℕ} {h : ∑ i, (m i + 1) = t + 1}
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)}

/-- Evaluation of an actual smooth opposite-parabolic section is locally constant.
The tensor carrier needs no topology. -/
theorem sectionEval_locallyConstant (f : Sections F h σ) :
    let := F.canonicalTopologicalData.topology
    IsLocallyConstant (sectionEval F h σ f) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
  obtain ⟨K, hK⟩ := f.property
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro x
  refine ⟨(fun k => x * k) '' (K : Set (GeneralLinear (t + 1) F.Carrier)),
    isOpenMap_mul_left x _ K.isOpen, ⟨1, K.one_mem, mul_one x⟩, ?_⟩
  rintro _ ⟨k, hk, rfl⟩
  exact congrArg (fun f' => f'.val x) (hK ⟨k, hk⟩)

/-- Every fixed block contraction of a smooth section is locally constant in the
ambient group coordinate. In particular, this applies at the Levi identity. -/
theorem scalarSection_locallyConstant (ell : ∀ i, W i →ₗ[ℂ] ℂ)
    (f : Sections F h σ) (a : (succBlockShape m h).Levi F.Carrier) :
    let := F.canonicalTopologicalData.topology
    IsLocallyConstant (fun g => scalarSection ell f g a) := by
  let := F.canonicalTopologicalData.topology
  exact (sectionEval_locallyConstant f).comp
    (fun v => tensorContraction ell ((succBlockShape m h).blockTensor σ a v))

end Sections

section Integrand

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable {t : ℕ} {m : Fin 2 → ℕ} {h : ∑ i, (m i + 1) = t + 1}
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)}
variable {ψ : letI := F.canonicalTopologicalData.topology
  UnitaryAdditiveCharacter F.Carrier}
variable [MeasurableSpace F.Carrier]
variable (ell : letI := F.canonicalTopologicalData.topology
  ∀ i, glInverseFunctionals ψ (m i) (σ i))
variable (f : Sections F h σ)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (GeneralLinear (t + 1) F.Carrier) V)
variable (hπ : letI := F.canonicalTopologicalData.topology; IsSmooth π)
variable (lambda : letI := F.canonicalTopologicalData.topology; glFunctionals ψ t π)
variable (Wtest : (coefficientModel π lambda).toSubmodule)
variable (Φ : letI := F.canonicalTopologicalData.topology
  SchwartzBruhat (Fin (t + 1) → F.Carrier))
variable (μ : letI := F.canonicalTopologicalData.topology; AdditiveHaarMeasure F.Carrier)

include hπ

omit [MeasurableSpace F.Carrier] in
/-- Actual coefficient-image functions of a smooth representation are locally
constant as scalar functions on the group. -/
theorem coefficient_locallyConstant :
    let := F.canonicalTopologicalData.topology
    IsLocallyConstant Wtest.val.val := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
  have hc := (Hecke.orbitMap_locallyConstant _ (model_isSmooth π hπ lambda Wtest)).comp
    (fun w : (coefficientModel π lambda).toSubmodule => w.val.val 1)
  change IsLocallyConstant (fun g => Wtest.val.val (1 * g)) at hc
  simpa only [one_mul] using hc

/-- The actual group integrand is locally constant. Smoothness of the test
representation is sufficient; no growth or convergence premise is used. -/
theorem groupIntegrand_locallyConstant :
    let := F.canonicalTopologicalData.topology
    IsLocallyConstant (groupIntegrand ell f Wtest.val Φ μ) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
  have hW := (coefficient_locallyConstant π hπ lambda Wtest).comp_continuous
    (continuous_const.mul continuous_id :
      Continuous (fun g : GeneralLinear (t + 1) F.Carrier =>
        blockRotation h F.Carrier * g))
  exact (hW.comp₂ (scalarSection_locallyConstant (fun i => (ell i).val) f 1) (· * ·)).comp₂
    (partialSection_locallyConstant h ψ μ Φ) (· * ·)

variable [@BorelSpace F.Carrier F.canonicalTopologicalData.topology _]

/-- Local constancy descends to the actual lower quotient using its quotient
topology and the proved representative-independent integrand. -/
theorem integrand_locallyConstant :
    let := F.canonicalTopologicalData.topology
    IsLocallyConstant (integrand ell f Wtest.val Φ μ) := by
  let := F.canonicalTopologicalData.topology
  change IsLocallyConstant (integrand ell f Wtest.val Φ μ)
  intro s
  apply (isQuotientMap_quotient_mk'
    (s := QuotientGroup.rightRel (lowerBlockUnipotent h F.Carrier))).isCoinducing.isOpen_preimage.mp
  exact groupIntegrand_locallyConstant ell f π hπ lambda Wtest Φ μ s

/-- The descended lower integrand is continuous. -/
theorem integrand_continuous :
    let := F.canonicalTopologicalData.topology
    Continuous (integrand ell f Wtest.val Φ μ) := by
  let := F.canonicalTopologicalData.topology
  exact (integrand_locallyConstant ell f π hπ lambda Wtest Φ μ).continuous

/-- The actual descended integrand bundled with its continuity certificate. -/
def continuousIntegrand :
    letI := F.canonicalTopologicalData.topology
    C(LowerQuotient h F.Carrier, ℂ) :=
  letI := F.canonicalTopologicalData.topology
  ⟨integrand ell f Wtest.val Φ μ, integrand_continuous ell f π hπ lambda Wtest Φ μ⟩

@[simp]
theorem continuousIntegrand_apply (q : LowerQuotient h F.Carrier) :
    continuousIntegrand ell f π hπ lambda Wtest Φ μ q =
      integrand ell f Wtest.val Φ μ q := rfl

/-- Borel measurability of the exact Section 4.7 lower integrand for every
supplied section, coefficient, row test and additive Fourier Haar measure. -/
theorem integrand_measurable
    [MeasurableSpace (LowerQuotient h F.Carrier)]
    [@BorelSpace (LowerQuotient h F.Carrier)
      (by letI := F.canonicalTopologicalData.topology; infer_instance) _] :
    Measurable (integrand ell f Wtest.val Φ μ) := by
  let := F.canonicalTopologicalData.topology
  exact (integrand_continuous ell f π hπ lambda Wtest Φ μ).measurable

end Integrand

end Langlands.RankinSelberg.TwoBlockLowerUnfolding
