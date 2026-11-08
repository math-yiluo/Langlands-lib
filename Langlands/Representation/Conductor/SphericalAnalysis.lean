import Langlands.Representation.Conductor.SphericalCoefficient
import Langlands.Representation.Conductor.SphericalIntegrals
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Local constancy and integration of Laurent quotient coefficients
-/

noncomputable section

namespace Langlands.Conductor

open MeasureTheory Langlands.GeneralLinear Langlands.Whittaker
open Langlands.HarmonicAnalysis Langlands.RankinSelberg
open Langlands.QuotientIntegration Langlands.GeneralLinear.Iwasawa

universe uX uA uF uV

section ScalarIntegrability

variable {X : Type uX} [TopologicalSpace X] [MeasurableSpace X]
variable [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
variable {A : Type uA} [AddCommGroup A] [Module ℂ A]

/-- A compactly supported locally constant function is scalar integrable
in its actual range span, without a topology on the coefficient space. -/
theorem isScalarIntegrable_coefficientSpanFunction_of_locallyConstant
    {f : X → A} (hf : IsLocallyConstant f) (hc : HasCompactSupport f) :
    IsScalarIntegrable μ (coefficientSpanFunction f) := by
  have hloc : IsLocallyConstant (coefficientSpanFunction f) :=
    IsLocallyConstant.desc (coefficientSpanFunction f) Subtype.val hf
      Subtype.val_injective
  have hs : HasCompactSupport (coefficientSpanFunction f) := by
    apply hc.mono
    intro x hx
    exact fun hz => hx (Subtype.ext hz)
  intro L
  exact (hloc.comp L).continuous.integrable_of_hasCompactSupport
    (hs.comp_left L.map_zero)

end ScalarIntegrability

section LocalConstancy

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable [IsNonarchimedeanLocalField F] {n : ℕ}

private theorem isLocallyConstant_of_integral_invariant {A : Type*}
    (f : Langlands.GeneralLinear (n + 1) F → A)
    (hf : ∀ (g k : Langlands.GeneralLinear (n + 1) F),
      k ∈ integralSubgroup (ValuativeRel.valuation F).integer n →
        f (g * k) = f g) :
    IsLocallyConstant f := by
  apply (IsLocallyConstant.iff_exists_open _).2
  intro g
  have hK := (levelOpenSubgroup F n 0).isOpen
  refine ⟨(fun h : Langlands.GeneralLinear (n + 1) F => g⁻¹ * h) ⁻¹'
      (levelOpenSubgroup F n 0 : Set (Langlands.GeneralLinear (n + 1) F)),
    hK.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · change g⁻¹ * g ∈ levelSubgroup F n 0
    rw [inv_mul_cancel]
    exact (levelSubgroup F n 0).one_mem
  · intro h hh
    have hk : g⁻¹ * h ∈ integralSubgroup (ValuativeRel.valuation F).integer n := by
      rw [← levelSubgroup_zero]
      exact hh
    simpa only [mul_inv_cancel_left] using hf g (g⁻¹ * h) hk

private theorem quotient_isLocallyConstant_of_pullback {A : Type*}
    (f : LeftUnipotentQuotient n F → A)
    (hf : IsLocallyConstant
      (fun g => f (leftQuotientMap (upperUnipotent (n + 1) F) g))) :
    IsLocallyConstant f := by
  intro S
  exact (leftQuotient_isOpenQuotientMap (upperUnipotent (n + 1) F)
    ).isQuotientMap.isCoinducing.isOpen_preimage.mp (hf S)

variable (abv : AbsoluteValue F ℝ)

/-- The determinant weight is locally constant when the absolute value is
trivial on valuation units. -/
theorem determinantWeight_isLocallyConstant
    (habv : ∀ x : F, ValuativeRel.valuation F x = 1 → abv x = 1) (s : ℂ) :
    IsLocallyConstant
      (fun g : Langlands.GeneralLinear (n + 1) F => determinantWeight abv g s) :=
  isLocallyConstant_of_integral_invariant _
    (fun g k hk => determinantWeight_mul_integral habv g k hk s)

variable {ϖ : Fˣ} (hϖ : IsUniformizingElement (ValuativeRel.valuation F) ϖ)

/-- The sum of the actual Iwasawa exponents is locally constant. -/
theorem sphericalQuotientDegree_isLocallyConstant :
    IsLocallyConstant (sphericalQuotientDegree (n := n) hϖ) := by
  apply quotient_isLocallyConstant_of_pullback
  apply isLocallyConstant_of_integral_invariant
  intro g k hk
  change ∑ i, exponent hϖ (g * k) i = ∑ i, exponent hϖ g i
  rw [exponent_mul_integral hϖ g hk]

variable (ψ : UnitaryAdditiveCharacter F) (q : ℕ)
variable (W : WhittakerFunctions ψ (n + 1))
variable (hψ : ∀ x ∈ (ValuativeRel.valuation F).integer, ψ x = 1)

include hψ in
/-- Local constancy of a Whittaker function gives local constancy of the actual
Laurent corank-one function. -/
theorem corankOnePolynomialFunction_isLocallyConstant
    (habv : ∀ x : F, ValuativeRel.valuation F x = 1 → abv x = 1)
    (hW : IsLocallyConstant W.val) :
    IsLocallyConstant (corankOnePolynomialFunction ψ abv hϖ q W) := by
  exact ((hW.comp_continuous (rankInclusionContinuous (R := F) 1).continuous).mul
    (determinantWeight_isLocallyConstant abv habv (0 - 1 / 2))).comp₂
      (sphericalWhittakerPolynomial_isLocallyConstant hϖ (inverseStandardCharacter ψ n) q
        (isIntegrallyTrivial_inverseStandardCharacter hψ n)) (· • ·)

/-- Local constancy descends to the actual upper-unipotent quotient. -/
theorem corankOnePolynomialIntegrand_isLocallyConstant
    (habv : ∀ x : F, ValuativeRel.valuation F x = 1 → abv x = 1)
    (hW : IsLocallyConstant W.val) :
    IsLocallyConstant (corankOnePolynomialIntegrand ψ abv hϖ q W hψ) :=
  quotient_isLocallyConstant_of_pullback _
    (corankOnePolynomialFunction_isLocallyConstant abv hϖ ψ q W hψ habv hW)

/-- Restricting the actual Laurent integrand to an Iwasawa degree preserves
local constancy. -/
theorem degreeCorankOnePolynomialIntegrand_isLocallyConstant
    (habv : ∀ x : F, ValuativeRel.valuation F x = 1 → abv x = 1)
    (hW : IsLocallyConstant W.val) (d : ℤ) :
    IsLocallyConstant (degreeCorankOnePolynomialIntegrand ψ abv hϖ q W hψ d) := by
  classical
  exact (sphericalQuotientDegree_isLocallyConstant hϖ).comp₂
    (corankOnePolynomialIntegrand_isLocallyConstant abv hϖ ψ q W hψ habv hW)
    (fun e p => if e = d then p else 0)

variable [MeasurableSpace (LeftUnipotentQuotient n F)]
variable [OpensMeasurableSpace (LeftUnipotentQuotient n F)]
variable (μ : Measure (LeftUnipotentQuotient n F)) [IsFiniteMeasureOnCompacts μ]

/-- Actual degree integrands with compact support satisfy the coefficient
integrability hypothesis for every measure finite on compact sets. -/
theorem degreeCorankOnePolynomialIntegrand_isScalarIntegrable
    (habv : ∀ x : F, ValuativeRel.valuation F x = 1 → abv x = 1)
    (hW : IsLocallyConstant W.val) (d : ℤ)
    (hc : HasCompactSupport (degreeCorankOnePolynomialIntegrand ψ abv hϖ q W hψ d)) :
    IsScalarIntegrable μ (coefficientSpanFunction
      (degreeCorankOnePolynomialIntegrand ψ abv hϖ q W hψ d)) :=
  isScalarIntegrable_coefficientSpanFunction_of_locallyConstant μ
    (degreeCorankOnePolynomialIntegrand_isLocallyConstant abv hϖ ψ q W hψ habv hW d) hc

end LocalConstancy

section SmoothModel

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable [IsNonarchimedeanLocalField F] {n : ℕ}
variable [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
variable [MeasurableSpace (upperUnipotent (n + 1) F)]
  [BorelSpace (upperUnipotent (n + 1) F)]
variable [MeasurableSpace (LeftUnipotentQuotient n F)]
  [MeasurableSpace (LeftUnipotentQuotient 0 F)]
variable {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
variable {ϖ : Fˣ} {μ : Measure (LeftUnipotentQuotient n F)}
variable (h : IsJacquetNormalization q ψ abv ϖ μ)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) V)
variable (hπ : IsSmooth π) (ℓ : glFunctionals ψ (n + 1) π)
variable (w : (coefficientModel π ℓ).toSubmodule)

/-- The actual degree integrand of a model vector, with the uniformizer and
character conductor supplied by the Jacquet normalization. -/
def degreeCorankOneModelIntegrand (d : ℤ) :
    LeftUnipotentQuotient n F → symmetricTorusSubalgebra (Fin (n + 1)) ℂ :=
  degreeCorankOnePolynomialIntegrand ψ abv h.uniformizer q w.val h.conductor.1 d

include hπ in
/-- For an actual smooth-model vector and a Jacquet-normalized quotient
measure, compact degree support implies scalar coefficient integrability. -/
theorem degreeCorankOnePolynomialIntegrand_model_isScalarIntegrable (d : ℤ)
    (hc : HasCompactSupport (degreeCorankOneModelIntegrand h π ℓ w d)) :
    IsScalarIntegrable μ
      (coefficientSpanFunction (degreeCorankOneModelIntegrand h π ℓ w d)) := by
  let : BorelSpace (LeftUnipotentQuotient n F) := h.borel
  let : μ.Regular := h.measure.regular
  exact degreeCorankOnePolynomialIntegrand_isScalarIntegrable abv h.uniformizer ψ q
    w.val h.conductor.1 μ h.abv_unit
    (glModelFunction_isLocallyConstant ψ (n + 1) π hπ ℓ w) d hc

end SmoothModel

end Langlands.Conductor
