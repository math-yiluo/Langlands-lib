import Langlands.Representation.GodementJacquet.SupercuspidalMatrixFunctionalEquationStatement
import Langlands.Representation.GodementJacquet.SupercuspidalMatrixRationalExtension
import Langlands.Representation.GodementJacquet.MonomialMatrixCoefficientSpan
import Langlands.Representation.GodementJacquet.SupercuspidalMatrixAssembly

/-! # The closed supercuspidal matrix functional equation -/

noncomputable section

namespace Langlands.GodementJacquet

open MeasureTheory HarmonicAnalysis RankinSelberg

universe uF uV

namespace Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance supercuspidalFinalTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance supercuspidalFinalValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance supercuspidalFinalLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance supercuspidalFinalT2 : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2
local instance supercuspidalFinalDisconnected : TotallyDisconnectedSpace F.Carrier :=
  (padicLatticeGeometry F F.canonicalTopologicalData).1
local instance supercuspidalFinalMeasurable : MeasurableSpace F.Carrier := borel _
local instance supercuspidalFinalBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance supercuspidalFinalGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance supercuspidalFinalGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Actual supercuspidality gives one Fourier monomial equation on all full
matrix tests and the whole bi-smooth coefficient span. -/
theorem exists_supercuspidalMatrixMonomialFunctionalEquation
    (hn : 0 < n)
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν)
    (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (hρ : GeneralLinear.IsSupercuspidal ρ) (hi : ρ.IsIrreducible) :
    ∃ (c : ℂˣ) (k : ℤ), HasMatrixMonomialFunctionalEquation F ψ ν ρ c k := by
  obtain ⟨c, k, hck⟩ :=
    exists_monomial_fourierRegular_inverseTranspose F hn ρ hρ hi ψ ν hsd
  have hι := GeneralLinear.isSupercuspidal_comp_inverseTranspose ρ hρ
  obtain ⟨ω, hRat⟩ := exists_supercuspidalMatrixRationalityData F ρ hρ hi
  have hR (ℓ : SmoothDual ρ) (Φ : MatrixTestFunction n F.Carrier) (v : V) :
      ∃ R, HasShiftedRationalValue F.canonicalTopologicalData.residueCardinality
        (normalizedAbsoluteValue F.canonicalTopologicalData)
        (generalLinearHaar F.Carrier n) Φ
        (matrixCoefficient ρ (smoothDualPairing ρ ℓ) v) R := by
    let w : smoothVectors ρ := ⟨v, hρ.1.1 v⟩
    let f : biSmoothMatrixCoefficients ρ :=
      ⟨biSmoothCoefficient ρ ℓ w, Submodule.subset_span ⟨ℓ, w, rfl⟩⟩
    obtain ⟨R, hR, _⟩ := hRat.2.2.1 Φ f
    exact ⟨R, hR⟩
  have hD (ℓ : SmoothDual ρ) (Φ : MatrixTestFunction n F.Carrier) (v : V) :
      ∃ R, HasShiftedRationalValue F.canonicalTopologicalData.residueCardinality
        (normalizedAbsoluteValue F.canonicalTopologicalData)
        (generalLinearHaar F.Carrier n) Φ
        (coefficientIota (matrixCoefficient ρ (smoothDualPairing ρ ℓ) v)) R := by
    let w : smoothVectors ρ := ⟨v, hρ.1.1 v⟩
    let f : biSmoothMatrixCoefficients ρ :=
      ⟨biSmoothCoefficient ρ ℓ w, Submodule.subset_span ⟨ℓ, w, rfl⟩⟩
    obtain ⟨R, hR, _⟩ := hRat.2.2.2 Φ f
    exact ⟨R, hR⟩
  refine ⟨shiftedMatrixMonomialUnit F n c k, k, ?_⟩
  intro Φ
  let ΦHat := rectangularFourierEquiv ψ ν (n + 1) (n + 1) hsd Φ
  refine ⟨ΦHat, ?_, ?_⟩
  · intro X
    exact ⟨rectangularFourierEquiv_integrable ψ ν (n + 1) (n + 1) hsd Φ X,
      rectangularFourierEquiv_apply ψ ν (n + 1) (n + 1) hsd Φ X⟩
  · intro f R RDual hRf hDf
    apply normalizedFunctionalEquation_of_biSmoothGenerators ρ
      F.canonicalTopologicalData.residueCardinality_gt_one
      (normalizedAbsoluteValue F.canonicalTopologicalData)
      (generalLinearHaar F.Carrier n) Φ ΦHat
      (shiftedMatrixMonomialUnit F n c k) k _ f R RDual hRf hDf
    intro ℓ v
    obtain ⟨S, hS⟩ := hR ℓ Φ v.val
    obtain ⟨E, hE⟩ := hD ℓ ΦHat v.val
    refine ⟨S, E, hS, hE, ?_⟩
    exact normalizedFunctionalEquation_of_supercuspidal_fourierRegular_operator
      F hn ρ hρ hi hι ψ ν hsd c k (smoothDualPairing ρ ℓ)
      (hR ℓ) (hD ℓ) hck Φ v.val S E hS hE

/-- Full normalized data, with both Euler polynomials one, for an actual
irreducible supercuspidal representation of rank greater than one. -/
theorem exists_supercuspidalMatrixFunctionalEquationData
    (hn : 0 < n)
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν)
    (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (hρ : GeneralLinear.IsSupercuspidal ρ) (hi : ρ.IsIrreducible) :
    ∃ (c : ℂˣ) (k : ℤ),
      NormalizedMatrixFunctionalEquationData F ψ ν ρ 1 1 c k := by
  obtain ⟨c, k, hFE⟩ :=
    exists_supercuspidalMatrixMonomialFunctionalEquation F hn ψ ν hsd ρ hρ hi
  exact ⟨c, k, normalizedMatrixFunctionalEquationData_of_supercuspidal_of_monomial
    F ψ ν hsd ρ hρ hi c k hFE⟩

end Padic

/-- The closed supercuspidal matrix functional-equation base, with the
canonical field structures and the supplied self-dual Fourier measure. -/
theorem supercuspidalMatrixFunctionalEquation :
    SupercuspidalMatrixFunctionalEquationStatement.{uF,uV} := by
  intro p hp F ψ ν hsd n V hV hModule ρ hρ hi
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let : MeasurableSpace F.Carrier := borel _
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
  let : MeasurableSpace (Langlands.GeneralLinear (n + 2) F.Carrier) := borel _
  let : BorelSpace (Langlands.GeneralLinear (n + 2) F.Carrier) := ⟨rfl⟩
  exact Padic.exists_supercuspidalMatrixFunctionalEquationData
    F (Nat.succ_pos n) ψ ν hsd ρ hρ hi

end Langlands.GodementJacquet
