import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonGLAdditive
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSingularNull
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonOrbitFourierExchange

/-! # The actual Fourier exchange on unipotent times general linear groups -/

noncomputable section

namespace Langlands.RankinSelberg.GLDeterminantDensity

open MeasureTheory HarmonicAnalysis GeneralLinear Whittaker Topology
open CompactWhittakerSynthesis

universe uF uH

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance glFourierTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance glFourierValuativeRel : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance glFourierLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance glFourierT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance glFourierSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance glFourierSigmaCompact : SigmaCompactSpace F.Carrier := F.canonicalTopologicalData.sigmaCompactSpace
local instance glFourierMeasurableSpace : MeasurableSpace F.Carrier := borel _
local instance glFourierBorelSpace : BorelSpace F.Carrier := ⟨rfl⟩
local instance glFourierGLMeasurableSpace (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance glFourierGLBorelSpace (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance glFourierGLLocallyCompact (n : ℕ) :
    LocallyCompactSpace (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace (n + 1)
local instance glFourierGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology (n + 1)
local instance glFourierNLocallyCompact (n : ℕ) :
    LocallyCompactSpace (upperUnipotent (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.upperUnipotentLocallyCompactSpace (n + 1)
local instance glFourierNSecondCountable (n : ℕ) :
    SecondCountableTopology (upperUnipotent (n + 1) F.Carrier) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance glFourierNMeasurableSpace (n : ℕ) : MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance glFourierNBorelSpace (n : ℕ) : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩


local instance glFourierTotallyDisconnected : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData

/-- The natural determinant power converts GL integrability to the full additive
matrix measure, since the singular locus is genuinely null. -/
theorem integrable_generalLinearHaar_natWeight_iff_full
    (ν : AdditiveHaarMeasure F.Carrier) (n : ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier → ℂ) :
    Integrable (fun g : Langlands.GeneralLinear (n + 1) F.Carrier =>
      determinantWeight abv g (n + 1 : ℕ) * A g.val)
      (generalLinearHaar F.Carrier n) ↔
    Integrable A (rectangularMeasure ν (n + 1) (n + 1)) := by
  simpa only [rectangularMeasure_restrict_generalLinear F ν (n + 1)] using
    integrable_generalLinearHaar_natWeight_iff F ν n A

/-- Full additive measure version, retaining the same fixed inverse scalar. -/
theorem integral_generalLinearHaar_natWeight_full
    (ν : AdditiveHaarMeasure F.Carrier) (n : ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier → ℂ) :
    (∫ g : Langlands.GeneralLinear (n + 1) F.Carrier,
      determinantWeight abv g (n + 1 : ℕ) * A g.val
        ∂generalLinearHaar F.Carrier n) =
    ((rectangularHaarScalar F ν n : ℝ) : ℂ)⁻¹ *
      ∫ X, A X ∂rectangularMeasure ν (n + 1) (n + 1) := by
  simpa only [rectangularMeasure_restrict_generalLinear F ν (n + 1)] using
    integral_generalLinearHaar_natWeight F ν n A

/-- Joint integrability with any s-finite auxiliary measure, on the full
additive matrix space and the unchanged general linear Haar measure. -/
theorem integrable_prod_generalLinearHaar_natWeight_iff_full
    {H : Type uH} [MeasurableSpace H] (μH : Measure H) [SFinite μH]
    (ν : AdditiveHaarMeasure F.Carrier) (n : ℕ)
    (A : H × Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier → ℂ) :
    Integrable (fun z : H × Langlands.GeneralLinear (n + 1) F.Carrier =>
      determinantWeight abv z.2 (n + 1 : ℕ) * A (z.1, z.2.val))
        (μH.prod (generalLinearHaar F.Carrier n)) ↔
    Integrable A (μH.prod (rectangularMeasure ν (n + 1) (n + 1))) := by
  simpa only [rectangularMeasure_restrict_generalLinear F ν (n + 1)] using
    integrable_prod_generalLinearHaar_natWeight_iff F μH ν n A

/-- Full product-measure identity; the auxiliary measure and integrand do not
change the one normalization scalar. -/
theorem integral_prod_generalLinearHaar_natWeight_full
    {H : Type uH} [MeasurableSpace H] (μH : Measure H) [SFinite μH]
    (ν : AdditiveHaarMeasure F.Carrier) (n : ℕ)
    (A : H × Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier → ℂ) :
    (∫ z : H × Langlands.GeneralLinear (n + 1) F.Carrier,
      determinantWeight abv z.2 (n + 1 : ℕ) * A (z.1, z.2.val)
        ∂μH.prod (generalLinearHaar F.Carrier n)) =
    ((rectangularHaarScalar F ν n : ℝ) : ℂ)⁻¹ *
      ∫ z, A z ∂μH.prod (rectangularMeasure ν (n + 1) (n + 1)) := by
  simpa only [rectangularMeasure_restrict_generalLinear F ν (n + 1)] using
    integral_prod_generalLinearHaar_natWeight F μH ν n A

/-- The actual dual Fourier orbit kernel with the natural GL determinant weight. -/
def unipotentGeneralLinearFourierDualKernel
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (n : ℕ)
    (Φ Ψ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    (z : upperUnipotent (n + 1) F.Carrier ×
      Langlands.GeneralLinear (n + 1) F.Carrier) : ℂ :=
  determinantWeight abv z.2 (n + 1 : ℕ) *
    unipotentMatrixFourierDualKernel ψ ν n Φ Ψ (z.1, z.2.val)

/-- The original orbit kernel with the identical natural GL determinant weight. -/
def unipotentGeneralLinearFourierOriginalKernel
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (n : ℕ)
    (Φ Ψ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    (z : upperUnipotent (n + 1) F.Carrier ×
      Langlands.GeneralLinear (n + 1) F.Carrier) : ℂ :=
  determinantWeight abv z.2 (n + 1 : ℕ) *
    unipotentMatrixFourierOriginalKernel ψ ν n Φ Ψ (z.1, z.2.val)

/-- Actual inverse-transpose/Weyl dual kernel convergence on N × GL, without
any invertible-support premise on the Fourier transform of Φ. -/
theorem integrable_generalLinear_unipotentMatrixFourierDualKernel
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (n : ℕ)
    (Φ Ψ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    (A q : ℤ) {a : ℕ} (ha : 0 < a)
    (hΨ : tsupport (Ψ : _ → ℂ) ⊆ RankOneBox.box F A q a) :
    Integrable (unipotentGeneralLinearFourierDualKernel F ψ ν n Φ Ψ)
      ((unipotentHaar F.Carrier n).prod (generalLinearHaar F.Carrier n)) := by
  exact (integrable_prod_generalLinearHaar_natWeight_iff_full F
    (unipotentHaar F.Carrier n) ν n _).2
      (integrable_unipotentMatrixFourierDualKernel F ψ ν hsd n Φ Ψ A q ha hΨ)

/-- Actual original kernel convergence on N × GL, from invertible support of
Φ and no additional support premise on Ψ. -/
theorem integrable_generalLinear_unipotentMatrixFourierOriginalKernel
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (n : ℕ)
    (Φ Ψ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    (hΦ : tsupport (Φ : _ → ℂ) ⊆
      Set.range (Units.val : Langlands.GeneralLinear (n + 1) F.Carrier →
        Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier)) :
    Integrable (unipotentGeneralLinearFourierOriginalKernel F ψ ν n Φ Ψ)
      ((unipotentHaar F.Carrier n).prod (generalLinearHaar F.Carrier n)) := by
  exact (integrable_prod_generalLinearHaar_natWeight_iff_full F
    (unipotentHaar F.Carrier n) ν n _).2
      (integrable_unipotentMatrixFourierOriginalKernel F ψ ν hsd n Φ Ψ hΦ)

/-- Each actual dual product integral has the same inverse scalar as every
other weighted GL integral, with no test-dependent normalization. -/
theorem integral_generalLinear_unipotentMatrixFourierDualKernel
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (n : ℕ)
    (Φ Ψ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier)) :
    (∫ z, unipotentGeneralLinearFourierDualKernel F ψ ν n Φ Ψ z
      ∂(unipotentHaar F.Carrier n).prod (generalLinearHaar F.Carrier n)) =
    ((rectangularHaarScalar F ν n : ℝ) : ℂ)⁻¹ *
      ∫ z, unipotentMatrixFourierDualKernel ψ ν n Φ Ψ z
        ∂(unipotentHaar F.Carrier n).prod
          (rectangularMeasure ν (n + 1) (n + 1)) :=
  integral_prod_generalLinearHaar_natWeight_full F (unipotentHaar F.Carrier n) ν n _

/-- The original product integral uses exactly the same normalization. -/
theorem integral_generalLinear_unipotentMatrixFourierOriginalKernel
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (n : ℕ)
    (Φ Ψ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier)) :
    (∫ z, unipotentGeneralLinearFourierOriginalKernel F ψ ν n Φ Ψ z
      ∂(unipotentHaar F.Carrier n).prod (generalLinearHaar F.Carrier n)) =
    ((rectangularHaarScalar F ν n : ℝ) : ℂ)⁻¹ *
      ∫ z, unipotentMatrixFourierOriginalKernel ψ ν n Φ Ψ z
        ∂(unipotentHaar F.Carrier n).prod
          (rectangularMeasure ν (n + 1) (n + 1)) :=
  integral_prod_generalLinearHaar_natWeight_full F (unipotentHaar F.Carrier n) ν n _

/-- Actual weighted Fourier exchange on N × GL; both product integrabilities
are proved and the identical normalization scalars cancel. -/
theorem generalLinear_unipotentMatrixFourier_exchange
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (n : ℕ)
    (Φ Ψ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    (hΦ : tsupport (Φ : _ → ℂ) ⊆
      Set.range (Units.val : Langlands.GeneralLinear (n + 1) F.Carrier →
        Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    (A q : ℤ) {a : ℕ} (ha : 0 < a)
    (hΨ : tsupport (Ψ : _ → ℂ) ⊆ RankOneBox.box F A q a) :
    Integrable (unipotentGeneralLinearFourierDualKernel F ψ ν n Φ Ψ)
      ((unipotentHaar F.Carrier n).prod (generalLinearHaar F.Carrier n)) ∧
    Integrable (unipotentGeneralLinearFourierOriginalKernel F ψ ν n Φ Ψ)
      ((unipotentHaar F.Carrier n).prod (generalLinearHaar F.Carrier n)) ∧
    (∫ z, unipotentGeneralLinearFourierDualKernel F ψ ν n Φ Ψ z
      ∂(unipotentHaar F.Carrier n).prod (generalLinearHaar F.Carrier n)) =
    ∫ z, unipotentGeneralLinearFourierOriginalKernel F ψ ν n Φ Ψ z
      ∂(unipotentHaar F.Carrier n).prod (generalLinearHaar F.Carrier n) := by
  refine ⟨integrable_generalLinear_unipotentMatrixFourierDualKernel
    F ψ ν hsd n Φ Ψ A q ha hΨ,
    integrable_generalLinear_unipotentMatrixFourierOriginalKernel
    F ψ ν hsd n Φ Ψ hΦ, ?_⟩
  rw [integral_generalLinear_unipotentMatrixFourierDualKernel F ψ ν n Φ Ψ,
    integral_generalLinear_unipotentMatrixFourierOriginalKernel F ψ ν n Φ Ψ,
    (unipotentMatrixFourier_exchange F ψ ν hsd n Φ Ψ hΦ A q ha hΨ).2.2]

/-- Fubini expresses the exchange as GL-outer integrals of the actual
unipotent averages. The natural determinant power is outside the inner average. -/
theorem generalLinear_unipotentMatrixFourier_exchange_averaged
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (n : ℕ)
    (Φ Ψ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    (hΦ : tsupport (Φ : _ → ℂ) ⊆
      Set.range (Units.val : Langlands.GeneralLinear (n + 1) F.Carrier →
        Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    (A q : ℤ) {a : ℕ} (ha : 0 < a)
    (hΨ : tsupport (Ψ : _ → ℂ) ⊆ RankOneBox.box F A q a) :
    (∫ g : Langlands.GeneralLinear (n + 1) F.Carrier,
      determinantWeight abv g (n + 1 : ℕ) *
        ∫ u : upperUnipotent (n + 1) F.Carrier,
          unipotentMatrixFourierDualKernel ψ ν n Φ Ψ (u, g.val)
          ∂unipotentHaar F.Carrier n
      ∂generalLinearHaar F.Carrier n) =
    ∫ g : Langlands.GeneralLinear (n + 1) F.Carrier,
      determinantWeight abv g (n + 1 : ℕ) *
        ∫ u : upperUnipotent (n + 1) F.Carrier,
          unipotentMatrixFourierOriginalKernel ψ ν n Φ Ψ (u, g.val)
          ∂unipotentHaar F.Carrier n
      ∂generalLinearHaar F.Carrier n := by
  obtain ⟨hd, ho, he⟩ :=
    generalLinear_unipotentMatrixFourier_exchange F ψ ν hsd n Φ Ψ hΦ A q ha hΨ
  rw [integral_prod_symm _ hd, integral_prod_symm _ ho] at he
  simpa only [unipotentGeneralLinearFourierDualKernel,
    unipotentGeneralLinearFourierOriginalKernel, integral_const_mul] using he

end Langlands.RankinSelberg.GLDeterminantDensity
