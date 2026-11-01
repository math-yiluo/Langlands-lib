import Langlands.Representation.RankinSelberg.AdjacentRankMatrixWitnesses
import Langlands.Representation.RankinSelberg.AdjacentRankMatrixReflection
import Langlands.Representation.RankinSelberg.RationalGammaComparison
import Langlands.Representation.RankinSelberg.WhittakerGammaAdapters
import Langlands.Representation.GodementJacquet.GenericMatrixFunctionalEquationProof
import Langlands.Representation.Twist.SubquotientProof

/-! Actual matrix functional equations for determinant-twisted adjacent test coefficients. -/

noncomputable section

set_option maxHeartbeats 800000

namespace Langlands.RankinSelberg.Padic

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear GodementJacquet
open scoped BigOperators

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance adjacentMatrixFETopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance adjacentMatrixFEValuative : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance adjacentMatrixFELocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance adjacentMatrixFET2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance adjacentMatrixFEDisconnected : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance adjacentMatrixFEMeasurable : MeasurableSpace F.Carrier := borel _
local instance adjacentMatrixFEBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance adjacentMatrixFEGLMeasurable (r : ℕ) :
    MeasurableSpace (GeneralLinear (r + 1) F.Carrier) := borel _
local instance adjacentMatrixFEGLBorel (r : ℕ) :
    BorelSpace (GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData
local notation "qF" => F.canonicalTopologicalData.residueCardinality

attribute [local irreducible] GodementJacquet.biSmoothMatrixCoefficients
  coefficientModel modelRepresentation

/-- The actual determinant-twisted test model, retaining the original
coefficient image and its right-translation action. -/
abbrev adjacentRankTwistedTestModel {r : ℕ}
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (ℓ : glFunctionals (ψ.scale (-1)) r τ) (χ : Quasicharacter F.Carrier) :=
  Langlands.twist (V := (glCoefficientModel (ψ.scale (-1)) r τ ℓ).toSubmodule)
    ((χ : F.Carrierˣ →* ℂˣ).comp determinant)
    (modelRepresentation τ ℓ)

/-- Literal shifted values and the unreflected Fourier equation for all
actual coefficients of a determinant twist. -/
def TwistedTestMatrixFunctionalEquationWitnesses {r : ℕ}
    (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier)
    (hself : IsSelfDual ψ μ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (χ : Quasicharacter F.Carrier)
    (P PD : Polynomial ℂ) (c : ℂˣ) (a : ℤ) : Prop :=
  ∀ (Φ : MatrixTestFunction r F.Carrier) (f : biSmoothMatrixCoefficients ρ),
    ∃ M MD : RationalFunctions,
      HasShiftedRationalValue qF abv (generalLinearHaar F.Carrier r) Φ
        (fun h => (χ (determinant h) : ℂ) * f.val h) M ∧
      HasShiftedRationalValue qF abv (generalLinearHaar F.Carrier r)
        (rectangularFourierEquiv ψ μ (r + 1) (r + 1) hself Φ)
        (fun h => (χ⁻¹ (determinant h) : ℂ) * coefficientIota f.val h) MD ∧
      NormalizedFunctionalEquation qF P PD 1 c 0 a M MD

/-- Supplied normalized data on the actual twisted test model give both
literal shifted rational values and their unreflected square Fourier equation.
The same constants apply to every square test and every actual coefficient. -/
abbrev AdjacentRankMatrixFunctionalEquationWitnesses {r : ℕ}
    (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier)
    (hself : IsSelfDual ψ μ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (ℓ : glFunctionals (ψ.scale (-1)) r τ) (χ : Quasicharacter F.Carrier)
    (P PD : Polynomial ℂ) (c : ℂˣ) (a : ℤ) : Prop :=
  TwistedTestMatrixFunctionalEquationWitnesses F ψ μ hself
    (V := (glCoefficientModel (ψ.scale (-1)) r τ ℓ).toSubmodule)
    (modelRepresentation τ ℓ) χ P PD c a

private theorem matrixWitnesses_of_twistedData {r : ℕ}
    (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier)
    (hself : IsSelfDual ψ μ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (χ : Quasicharacter F.Carrier)
    (P PD : Polynomial ℂ) (c : ℂˣ) (a : ℤ)
    (hdata : GodementJacquet.Padic.NormalizedMatrixFunctionalEquationData F ψ μ
      (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) ρ) P PD c a) :
    TwistedTestMatrixFunctionalEquationWitnesses F ψ μ hself ρ χ P PD c a := by
  intro Φ f
  let fT : biSmoothMatrixCoefficients
      (V := V)
      (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) ρ) := biSmoothCoefficientTwist
    (V := V)
    ((χ : F.Carrierˣ →* ℂˣ).comp determinant)
    (determinantCharacter_openKernel (F := F.Carrier) (n := r)
      (χ : F.Carrierˣ →* ℂˣ)
      (quasicharacter_isOpen_ker F.canonicalTopologicalData χ)) ρ f
  obtain ⟨ΦHat, hΦHat, hFE⟩ := hdata.2.2 Φ
  have hΦ : ΦHat = rectangularFourierEquiv ψ μ (r + 1) (r + 1) hself Φ := by
    ext x
    exact (hΦHat x).2.trans (rectangularFourierEquiv_apply ψ μ _ _ hself Φ x).symm
  obtain ⟨M, hM⟩ := hdata.1.2.1 Φ fT
  obtain ⟨MD, hMD⟩ := hdata.2.1.2.1 ΦHat fT
  have hfD : coefficientIota fT.val = fun h =>
      (χ⁻¹ (determinant h) : ℂ) * coefficientIota f.val h := by
    exact coefficientIota_determinantTwist χ f.val
  refine ⟨M, MD, hM, ?_, ?_⟩
  · simpa only [hfD, hΦ] using hMD
  · exact hFE fT M MD hM hMD

/-- The Fourier witness of the normalized data is exactly the canonical
square Fourier transform, so its equation concerns the required literal tests. -/
theorem adjacentRankMatrixFunctionalEquationWitnesses_of_data {r : ℕ}
    (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier)
    (hself : IsSelfDual ψ μ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (ℓ : glFunctionals (ψ.scale (-1)) r τ) (χ : Quasicharacter F.Carrier)
    (P PD : Polynomial ℂ) (c : ℂˣ) (a : ℤ)
    (hdata : GodementJacquet.Padic.NormalizedMatrixFunctionalEquationData F ψ μ
      (V := (glCoefficientModel (ψ.scale (-1)) r τ ℓ).toSubmodule)
      (adjacentRankTwistedTestModel F ψ τ ℓ χ) P PD c a) :
    AdjacentRankMatrixFunctionalEquationWitnesses F ψ μ hself τ ℓ χ P PD c a := by
  exact matrixWitnesses_of_twistedData F ψ μ hself
    (V := (glCoefficientModel (ψ.scale (-1)) r τ ℓ).toSubmodule)
    (modelRepresentation τ ℓ) χ P PD c a hdata

end Langlands.RankinSelberg.Padic
