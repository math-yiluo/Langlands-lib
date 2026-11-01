import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonCompactOrbitIntegration
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonScalarHaar

/-! Natural GL₁ weights in the same-kernel compact Fourier/block identity. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear

universe uF uX

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance compactGLTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance compactGLValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance compactGLLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance compactGLT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance compactGLSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance compactGLSigmaCompact : SigmaCompactSpace F.Carrier :=
  F.canonicalTopologicalData.sigmaCompactSpace
local instance compactGLMeasurable : MeasurableSpace F.Carrier := borel _
local instance compactGLBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance compactGLTotallyDisconnected : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance compactGLNMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance compactGLNBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
local instance compactGLGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance compactGLGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance compactGLGLLocallyCompact (n : ℕ) :
    LocallyCompactSpace (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace (n + 1)
local instance compactGLGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology (n + 1)

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData

variable {X : Type uX} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X]

/-- The same compact Fourier orbit, integrated over unipotents and weighted
with the natural GL₁ determinant exponent. -/
def compactSignedWeylGLIntegrand
    (μ : Measure X) (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : AdditiveHaarMeasure F.Carrier) (m : ℕ)
    (U : X → Langlands.GeneralLinear (m + 2) F.Carrier) (κ : SchwartzBruhat X)
    (Φ : SchwartzBruhat (Matrix (Fin (m + 2)) (Fin (m + 2)) F.Carrier))
    (g : Langlands.GeneralLinear 1 F.Carrier) : ℂ :=
  determinantWeight abv g 1 * ∫ u,
    compactSignedWeylOrbitFourierAverage F μ ψ ν m U κ Φ (u, g 0 0)
      ∂unipotentHaar F.Carrier (m + 1)

/-- The same compact original orbit, with the identical GL₁ weight and the
actual complementary block variable retained. -/
def compactSignedBlockGLIntegrand
    (μ : Measure X) (ψ : UnitaryAdditiveCharacter F.Carrier)
    (m : ℕ)
    (U : X → Langlands.GeneralLinear (m + 2) F.Carrier) (κ : SchwartzBruhat X)
    (Φ : SchwartzBruhat (Matrix (Fin (m + 2)) (Fin (m + 2)) F.Carrier))
    (z : Langlands.GeneralLinear 1 F.Carrier ×
      Matrix (Fin m) (Fin 1) F.Carrier) : ℂ :=
  determinantWeight abv z.1 1 * ∫ u,
    compactSignedBlockOrbitAverage F μ ψ m U κ Φ (u, (z.1 0 0, z.2))
      ∂unipotentHaar F.Carrier (m + 1)

set_option maxHeartbeats 800000 in
/-- The actual Fourier and complementary-block averages have convergent
natural-weight GL₁ integrals, with equal values and no extra scale factor. -/
theorem compact_signedWeylGL_blockGL_fourier_duality
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] [SFinite μ]
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (m : ℕ)
    (U : X → Langlands.GeneralLinear (m + 2) F.Carrier) (hU : Continuous U)
    (κ : SchwartzBruhat X)
    (hunit : ∀ x, κ x ≠ 0 →
      F.canonicalTopologicalData.determinantNorm (m + 2) (U x) = 1)
    (Φ : SchwartzBruhat (Matrix (Fin (m + 2)) (Fin (m + 2)) F.Carrier)) :
    Integrable (compactSignedWeylGLIntegrand F μ ψ ν m U κ Φ)
      (generalLinearHaar F.Carrier 0) ∧
    Integrable (compactSignedBlockGLIntegrand F μ ψ m U κ Φ)
      ((generalLinearHaar F.Carrier 0).prod (rectangularMeasure ν m 1)) ∧
    (∫ g, compactSignedWeylGLIntegrand F μ ψ ν m U κ Φ g
      ∂generalLinearHaar F.Carrier 0) =
    ∫ z, compactSignedBlockGLIntegrand F μ ψ m U κ Φ z
      ∂(generalLinearHaar F.Carrier 0).prod (rectangularMeasure ν m 1) := by
  obtain ⟨hl, hr, he⟩ := compact_signedWeylOrbit_blockOrbit_fourier_duality_averaged
    F μ ψ ν hsd m U hU κ hunit Φ
  let A : F.Carrier → ℂ := fun a => ∫ u,
    compactSignedWeylOrbitFourierAverage F μ ψ ν m U κ Φ (u, a)
      ∂unipotentHaar F.Carrier (m + 1)
  let B : F.Carrier × Matrix (Fin m) (Fin 1) F.Carrier → ℂ := fun z => ∫ u,
    compactSignedBlockOrbitAverage F μ ψ m U κ Φ (u, z)
      ∂unipotentHaar F.Carrier (m + 1)
  have hli := (integrable_generalLinear_one_natWeight_iff F ν A).2 hl
  have hri := (integrable_generalLinear_one_prod_natWeight_iff
    F (rectangularMeasure ν m 1) ν B).2 hr
  refine ⟨hli, hri, ?_⟩
  exact (integral_generalLinear_one_natWeight F ν A).trans
    ((congrArg (fun z : ℂ =>
      ((GLDeterminantDensity.rectangularHaarScalar F ν 0 : ℝ) : ℂ)⁻¹ * z)
      (he.trans (integral_prod B hr).symm)).trans
        (integral_generalLinear_one_prod_natWeight F (rectangularMeasure ν m 1) ν B).symm)

/-- Fubini gives the convergent block-integrated GL₁ form of the same identity. -/
theorem compact_signedWeylGL_blockGL_fourier_duality_iterated
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] [SFinite μ]
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (m : ℕ)
    (U : X → Langlands.GeneralLinear (m + 2) F.Carrier) (hU : Continuous U)
    (κ : SchwartzBruhat X)
    (hunit : ∀ x, κ x ≠ 0 →
      F.canonicalTopologicalData.determinantNorm (m + 2) (U x) = 1)
    (Φ : SchwartzBruhat (Matrix (Fin (m + 2)) (Fin (m + 2)) F.Carrier)) :
    Integrable (fun g : Langlands.GeneralLinear 1 F.Carrier =>
      ∫ Z, compactSignedBlockGLIntegrand F μ ψ m U κ Φ (g, Z)
        ∂rectangularMeasure ν m 1) (generalLinearHaar F.Carrier 0) ∧
    (∫ g, compactSignedWeylGLIntegrand F μ ψ ν m U κ Φ g
      ∂generalLinearHaar F.Carrier 0) =
    ∫ g : Langlands.GeneralLinear 1 F.Carrier,
      ∫ Z, compactSignedBlockGLIntegrand F μ ψ m U κ Φ (g, Z)
        ∂rectangularMeasure ν m 1 ∂generalLinearHaar F.Carrier 0 := by
  obtain ⟨_, hr, he⟩ := compact_signedWeylGL_blockGL_fourier_duality
    F μ ψ ν hsd m U hU κ hunit Φ
  exact ⟨hr.integral_prod_left, he.trans (integral_prod _ hr)⟩

end Langlands.RankinSelberg
