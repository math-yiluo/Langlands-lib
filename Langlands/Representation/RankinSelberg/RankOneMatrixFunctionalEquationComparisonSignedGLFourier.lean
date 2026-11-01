import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonGLFourierBridge
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSignedOrbitFourier

/-! # The actual signed Fourier exchange on unipotent times general linear groups -/

noncomputable section

namespace Langlands.RankinSelberg.GLDeterminantDensity

open MeasureTheory HarmonicAnalysis GeneralLinear Whittaker Topology
open CompactWhittakerSynthesis

universe uF uH

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance signedGLFourierTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance signedGLFourierValuativeRel : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance signedGLFourierLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance signedGLFourierT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance signedGLFourierSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance signedGLFourierSigmaCompact : SigmaCompactSpace F.Carrier := F.canonicalTopologicalData.sigmaCompactSpace
local instance signedGLFourierMeasurableSpace : MeasurableSpace F.Carrier := borel _
local instance signedGLFourierBorelSpace : BorelSpace F.Carrier := ⟨rfl⟩
local instance signedGLFourierGLMeasurableSpace (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance signedGLFourierGLBorelSpace (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance signedGLFourierGLLocallyCompact (n : ℕ) :
    LocallyCompactSpace (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace (n + 1)
local instance signedGLFourierGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology (n + 1)
local instance signedGLFourierNLocallyCompact (n : ℕ) :
    LocallyCompactSpace (upperUnipotent (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.upperUnipotentLocallyCompactSpace (n + 1)
local instance signedGLFourierNSecondCountable (n : ℕ) :
    SecondCountableTopology (upperUnipotent (n + 1) F.Carrier) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance signedGLFourierNMeasurableSpace (n : ℕ) : MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance signedGLFourierNBorelSpace (n : ℕ) : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩


local instance signedGLFourierTotallyDisconnected : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData

/-- The actual dual Fourier orbit kernel with the natural GL determinant weight. -/
def signedUnipotentGeneralLinearFourierDualKernel
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (n : ℕ)
    (Φ Ψ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    (z : upperUnipotent (n + 1) F.Carrier ×
      Langlands.GeneralLinear (n + 1) F.Carrier) : ℂ :=
  determinantWeight abv z.2 (n + 1 : ℕ) *
    signedUnipotentMatrixFourierDualKernel ψ ν n Φ Ψ (z.1, z.2.val)

/-- The original orbit kernel with the identical natural GL determinant weight. -/
def signedUnipotentGeneralLinearFourierOriginalKernel
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (n : ℕ)
    (Φ Ψ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    (z : upperUnipotent (n + 1) F.Carrier ×
      Langlands.GeneralLinear (n + 1) F.Carrier) : ℂ :=
  determinantWeight abv z.2 (n + 1 : ℕ) *
    signedUnipotentMatrixFourierOriginalKernel ψ ν n Φ Ψ (z.1, z.2.val)

/-- Actual inverse-transpose/Weyl dual kernel convergence on N × GL, without
any invertible-support premise on the Fourier transform of Φ. -/
theorem integrable_generalLinear_signedUnipotentMatrixFourierDualKernel
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (n : ℕ)
    (Φ Ψ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    (A q : ℤ) {a : ℕ} (ha : 0 < a)
    (hΨ : tsupport (Ψ : _ → ℂ) ⊆ RankOneBox.box F A q a) :
    Integrable (signedUnipotentGeneralLinearFourierDualKernel F ψ ν n Φ Ψ)
      ((unipotentHaar F.Carrier n).prod (generalLinearHaar F.Carrier n)) := by
  exact (integrable_prod_generalLinearHaar_natWeight_iff_full F
    (unipotentHaar F.Carrier n) ν n _).2
      (integrable_signedUnipotentMatrixFourierDualKernel F ψ ν hsd n Φ Ψ A q ha hΨ)

/-- Actual original kernel convergence on N × GL, from invertible support of
Φ and no additional support premise on Ψ. -/
theorem integrable_generalLinear_signedUnipotentMatrixFourierOriginalKernel
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (n : ℕ)
    (Φ Ψ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    (hΦ : tsupport (Φ : _ → ℂ) ⊆
      Set.range (Units.val : Langlands.GeneralLinear (n + 1) F.Carrier →
        Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier)) :
    Integrable (signedUnipotentGeneralLinearFourierOriginalKernel F ψ ν n Φ Ψ)
      ((unipotentHaar F.Carrier n).prod (generalLinearHaar F.Carrier n)) := by
  exact (integrable_prod_generalLinearHaar_natWeight_iff_full F
    (unipotentHaar F.Carrier n) ν n _).2
      (integrable_signedUnipotentMatrixFourierOriginalKernel F ψ ν hsd n Φ Ψ hΦ)

/-- Each actual dual product integral has the same inverse scalar as every
other weighted GL integral, with no test-dependent normalization. -/
theorem integral_generalLinear_signedUnipotentMatrixFourierDualKernel
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (n : ℕ)
    (Φ Ψ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier)) :
    (∫ z, signedUnipotentGeneralLinearFourierDualKernel F ψ ν n Φ Ψ z
      ∂(unipotentHaar F.Carrier n).prod (generalLinearHaar F.Carrier n)) =
    ((rectangularHaarScalar F ν n : ℝ) : ℂ)⁻¹ *
      ∫ z, signedUnipotentMatrixFourierDualKernel ψ ν n Φ Ψ z
        ∂(unipotentHaar F.Carrier n).prod
          (rectangularMeasure ν (n + 1) (n + 1)) :=
  integral_prod_generalLinearHaar_natWeight_full F (unipotentHaar F.Carrier n) ν n _

/-- The original product integral uses exactly the same normalization. -/
theorem integral_generalLinear_signedUnipotentMatrixFourierOriginalKernel
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (n : ℕ)
    (Φ Ψ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier)) :
    (∫ z, signedUnipotentGeneralLinearFourierOriginalKernel F ψ ν n Φ Ψ z
      ∂(unipotentHaar F.Carrier n).prod (generalLinearHaar F.Carrier n)) =
    ((rectangularHaarScalar F ν n : ℝ) : ℂ)⁻¹ *
      ∫ z, signedUnipotentMatrixFourierOriginalKernel ψ ν n Φ Ψ z
        ∂(unipotentHaar F.Carrier n).prod
          (rectangularMeasure ν (n + 1) (n + 1)) :=
  integral_prod_generalLinearHaar_natWeight_full F (unipotentHaar F.Carrier n) ν n _

/-- Actual weighted Fourier exchange on N × GL; both product integrabilities
are proved and the identical normalization scalars cancel. -/
theorem generalLinear_signedUnipotentMatrixFourier_exchange
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (n : ℕ)
    (Φ Ψ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    (hΦ : tsupport (Φ : _ → ℂ) ⊆
      Set.range (Units.val : Langlands.GeneralLinear (n + 1) F.Carrier →
        Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    (A q : ℤ) {a : ℕ} (ha : 0 < a)
    (hΨ : tsupport (Ψ : _ → ℂ) ⊆ RankOneBox.box F A q a) :
    Integrable (signedUnipotentGeneralLinearFourierDualKernel F ψ ν n Φ Ψ)
      ((unipotentHaar F.Carrier n).prod (generalLinearHaar F.Carrier n)) ∧
    Integrable (signedUnipotentGeneralLinearFourierOriginalKernel F ψ ν n Φ Ψ)
      ((unipotentHaar F.Carrier n).prod (generalLinearHaar F.Carrier n)) ∧
    (∫ z, signedUnipotentGeneralLinearFourierDualKernel F ψ ν n Φ Ψ z
      ∂(unipotentHaar F.Carrier n).prod (generalLinearHaar F.Carrier n)) =
    ∫ z, signedUnipotentGeneralLinearFourierOriginalKernel F ψ ν n Φ Ψ z
      ∂(unipotentHaar F.Carrier n).prod (generalLinearHaar F.Carrier n) := by
  refine ⟨integrable_generalLinear_signedUnipotentMatrixFourierDualKernel
    F ψ ν hsd n Φ Ψ A q ha hΨ,
    integrable_generalLinear_signedUnipotentMatrixFourierOriginalKernel
    F ψ ν hsd n Φ Ψ hΦ, ?_⟩
  rw [integral_generalLinear_signedUnipotentMatrixFourierDualKernel F ψ ν n Φ Ψ,
    integral_generalLinear_signedUnipotentMatrixFourierOriginalKernel F ψ ν n Φ Ψ,
    (signedUnipotentMatrixFourier_exchange F ψ ν hsd n Φ Ψ hΦ A q ha hΨ).2.2]

/-- Fubini expresses the exchange as GL-outer integrals of the actual
unipotent averages. The natural determinant power is outside the inner average. -/
theorem generalLinear_signedUnipotentMatrixFourier_exchange_averaged
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
          signedUnipotentMatrixFourierDualKernel ψ ν n Φ Ψ (u, g.val)
          ∂unipotentHaar F.Carrier n
      ∂generalLinearHaar F.Carrier n) =
    ∫ g : Langlands.GeneralLinear (n + 1) F.Carrier,
      determinantWeight abv g (n + 1 : ℕ) *
        ∫ u : upperUnipotent (n + 1) F.Carrier,
          signedUnipotentMatrixFourierOriginalKernel ψ ν n Φ Ψ (u, g.val)
          ∂unipotentHaar F.Carrier n
      ∂generalLinearHaar F.Carrier n := by
  obtain ⟨hd, ho, he⟩ :=
    generalLinear_signedUnipotentMatrixFourier_exchange F ψ ν hsd n Φ Ψ hΦ A q ha hΨ
  rw [integral_prod_symm _ hd, integral_prod_symm _ ho] at he
  simpa only [signedUnipotentGeneralLinearFourierDualKernel,
    signedUnipotentGeneralLinearFourierOriginalKernel, integral_const_mul] using he

end Langlands.RankinSelberg.GLDeterminantDensity
