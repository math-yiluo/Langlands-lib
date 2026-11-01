import Langlands.Representation.RankinSelberg.CorankOneEntireSliceProof
import Langlands.Representation.RankinSelberg.TwoBlockSecondWhittakerDeformationStatement
import Langlands.Representation.RankinSelberg.AdjacentRankClearingKernel

/-! Actual corank coefficient families and specialization of their Laurent clearing. -/

noncomputable section

namespace Langlands.RankinSelberg.Padic

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
open ParameterSpecialization
open scoped BigOperators

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance entireCoefficientTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance entireCoefficientValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance entireCoefficientLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance entireCoefficientFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance entireCoefficientFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance entireCoefficientGroupMeasurable (r : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (r + 1) F.Carrier) := borel _
local instance entireCoefficientGroupBorel (r : ℕ) :
    BorelSpace (Langlands.GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
local instance entireCoefficientUnipotentMeasurable (r : ℕ) :
    MeasurableSpace (upperUnipotent (r + 1) F.Carrier) := borel _
local instance entireCoefficientUnipotentBorel (r : ℕ) :
    BorelSpace (upperUnipotent (r + 1) F.Carrier) := ⟨rfl⟩
local instance entireCoefficientQuotientMeasurable (r : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient r F.Carrier) := borel _
local instance entireCoefficientQuotientBorel (r : ℕ) :
    BorelSpace (LeftUnipotentQuotient r F.Carrier) := ⟨rfl⟩

local notation "T" => F.canonicalTopologicalData
local notation "abv" => normalizedAbsoluteValue T

/-- One compact open right level for the whole actual Whittaker family. -/
def HasCommonCompactOpenRightLevel {r : ℕ}
    {ψ : UnitaryAdditiveCharacter F.Carrier} (U : ℂ → WhittakerFunctions ψ r) : Prop :=
  ∃ K : Subgroup (Langlands.GeneralLinear (r + 1) F.Carrier),
    IsOpen (K : Set (Langlands.GeneralLinear (r + 1) F.Carrier)) ∧
    IsCompact (K : Set (Langlands.GeneralLinear (r + 1) F.Carrier)) ∧
    ∀ (u : ℂ) (g : Langlands.GeneralLinear (r + 1) F.Carrier) (k : K),
      (U u).val (g * k) = (U u).val g

/-- The literal determinant-slice coefficients at spectral parameter zero. -/
def corankCoefficientFamily {r : ℕ} (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : Measure (LeftUnipotentQuotient r F.Carrier))
    (Wprime : InverseWhittakerFunctions ψ r)
    (U : ℂ → WhittakerFunctions ψ (r + 1)) : ℂ → BilateralLaurentSeries :=
  fun u m => sliceCoefficient T ν (corankOneIntegrand ψ abv (U u) Wprime 0) m

/-- The published corank slice theorem supplies integrability and entire
dependence for the actual coefficient family, with its original measure. -/
theorem corankCoefficientFamily_integrable_entire
    (ψ : UnitaryAdditiveCharacter F.Carrier) (r : ℕ)
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier r)]
    (ν : Measure (LeftUnipotentQuotient r F.Carrier))
    (hν : IsCompatible (upperUnipotent (r + 1) F.Carrier)
      (generalLinearHaar F.Carrier r) (unipotentHaar F.Carrier r) ν)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (hτ : IsOfWhittakerType r (inverseStandardCharacter ψ r) τ)
    (ℓ : glInverseFunctionals ψ r τ) (Wprime : (coefficientModel τ ℓ).toSubmodule)
    (U : ℂ → WhittakerFunctions ψ (r + 1))
    (hK : HasCommonCompactOpenRightLevel F U)
    (hU : ∀ g u, AnalyticAt ℂ (fun z => (U z).val g) u) :
    (∀ u, SliceIntegrable T ν (corankOneIntegrand ψ abv (U u) Wprime.val 0)) ∧
      EntireCoefficientFamily (corankCoefficientFamily F ψ ν Wprime.val U) := by
  have hs := corankOneEntireSlice p F ψ r ν hν V τ hτ ℓ Wprime U hK hU
  exact ⟨fun u m => (hs m).1 u, fun m u => (hs m).2 u⟩

/-- Formal real-ray clearing of these actual coefficients specializes to zero.
The corank slice theorem discharges the integral-analyticity premise. -/
theorem corankCoefficientFamily_clearing_at_zero
    (ψ : UnitaryAdditiveCharacter F.Carrier) (r : ℕ)
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier r)]
    (ν : Measure (LeftUnipotentQuotient r F.Carrier))
    (hν : IsCompatible (upperUnipotent (r + 1) F.Carrier)
      (generalLinearHaar F.Carrier r) (unipotentHaar F.Carrier r) ν)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (hτ : IsOfWhittakerType r (inverseStandardCharacter ψ r) τ)
    (ℓ : glInverseFunctionals ψ r τ) (Wprime : (coefficientModel τ ℓ).toSubmodule)
    (U : ℂ → WhittakerFunctions ψ (r + 1))
    (hK : HasCommonCompactOpenRightLevel F U)
    (hU : ∀ g u, AnalyticAt ℂ (fun z => (U z).val g) u)
    (P₀ P₁ : Polynomial ℂ) (C : ℝ)
    (hreal : ∀ u : ℝ, C < u → ∃ R : LaurentPolynomial ℂ,
      BilateralLaurentSeries.ofLaurentPolynomial R =
        spectralClearingKernel F.canonicalTopologicalData.residueCardinality P₀ P₁ (u : ℂ) •
          corankCoefficientFamily F ψ ν Wprime.val U (u : ℂ)) :
    ∃ R : LaurentPolynomial ℂ,
      BilateralLaurentSeries.ofLaurentPolynomial R = (P₀ * P₁).toLaurent •
        corankCoefficientFamily F ψ ν Wprime.val U 0 := by
  have hc := (corankCoefficientFamily_integrable_entire
    F ψ r ν hν τ hτ ℓ Wprime U hK hU).2
  exact spectralKernel_laurent_clearing_at_zero
    F.canonicalTopologicalData.residueCardinality_gt_one P₀ P₁
    (corankCoefficientFamily F ψ ν Wprime.val U) hc C hreal

/-- The second-block deformation proposition extends every actual coefficient
image vector to Whittaker functions, retaining all coefficient realizations. -/
theorem secondBlock_whittakerFamily
    (hdeform : TwoBlockSecondWhittakerDeformationStatement.{uF,uW})
    (ψ : UnitaryAdditiveCharacter F.Carrier) (t : ℕ)
    (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = t + 1)
    {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (W i))
    (hσ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i))
    (ℓ₀ : glFunctionals ψ t (twoBlockSecondDeformedInduced F m h σ 0))
    (hℓ₀ : ℓ₀.val ≠ 0)
    (W₀ : (coefficientModel (twoBlockSecondDeformedInduced F m h σ 0) ℓ₀).toSubmodule) :
    ∃ U : ℂ → WhittakerFunctions ψ t,
      U 0 = W₀.val ∧
      (∀ u : ℂ, ∃ ℓ : glFunctionals ψ t (twoBlockSecondDeformedInduced F m h σ u),
        ℓ.val ≠ 0 ∧ ∃ v, coefficientMap (twoBlockSecondDeformedInduced F m h σ u) ℓ v =
          U u) ∧
      HasCommonCompactOpenRightLevel F U ∧
      ∀ g u, AnalyticAt ℂ (fun z => (U z).val g) u := by
  obtain ⟨v₀, hv₀⟩ :=
    modelMap_surjective (twoBlockSecondDeformedInduced F m h σ 0) ℓ₀ W₀
  obtain ⟨Wu, hzero, hcoeff, hlevel, hanalytic⟩ :=
    hdeform p F ψ t m h σ hσ ℓ₀ hℓ₀ v₀
  let U : ℂ → WhittakerFunctions ψ t := fun u =>
    ⟨Wu u, by
      obtain ⟨ℓ, -, v, hv⟩ := hcoeff u
      intro n g
      change Wu u ((n : Langlands.GeneralLinear (t + 1) F.Carrier) * g) =
        (standardCharacter ψ t n : ℂ) * Wu u g
      rw [hv, hv, map_mul, Module.End.mul_apply]
      exact ℓ.property n _⟩
  refine ⟨U, ?_, ?_, hlevel, hanalytic⟩
  · apply Subtype.ext
    funext g
    have hvalue := congrArg (fun w => w.val.val g) hv₀
    exact (hzero g).trans hvalue
  · intro u
    obtain ⟨ℓ, hℓ, v, hv⟩ := hcoeff u
    refine ⟨ℓ, hℓ, v, ?_⟩
    apply Subtype.ext
    funext g
    exact (hv g).symm

end Langlands.RankinSelberg.Padic
