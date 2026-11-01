import Langlands.Representation.GodementJacquet.SupercuspidalMatrixRationality
import Langlands.Representation.GodementJacquet.MatrixDenominatorCancellation
import Langlands.Representation.GodementJacquet.MatrixUnitValueProof
import Langlands.HarmonicAnalysis.RectangularFourierEquiv

/-! # Supercuspidal matrix analytic data from the raw monomial equation -/

noncomputable section

namespace Langlands.GodementJacquet.Padic

open MeasureTheory HarmonicAnalysis RankinSelberg LocalFactor

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance supercuspidalMatrixAssemblyTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance supercuspidalMatrixAssemblyValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance supercuspidalMatrixAssemblyLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance supercuspidalMatrixAssemblyT2 : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2
local instance supercuspidalMatrixAssemblyMeasurable : MeasurableSpace F.Carrier := borel _
local instance supercuspidalMatrixAssemblyBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance supercuspidalMatrixAssemblyTotallyDisconnected :
    TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance supercuspidalMatrixAssemblyGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance supercuspidalMatrixAssemblyGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The raw Fourier and monomial equation, without convergence, rational
existence or normalized-generator assertions. Fourier witnesses precede every
coefficient and both actual continuation guards are retained. -/
def HasMatrixMonomialFunctionalEquation
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (c : ℂˣ) (m : ℤ) : Prop :=
  ∀ Φ : MatrixTestFunction n F.Carrier, ∃ ΦHat : MatrixTestFunction n F.Carrier,
    MatrixFourierPair F ψ ν Φ ΦHat ∧
    ∀ f : biSmoothMatrixCoefficients ρ, ∀ R RDual : RationalFunctions,
      HasShiftedRationalValue F.canonicalTopologicalData.residueCardinality
        (normalizedAbsoluteValue F.canonicalTopologicalData)
        (generalLinearHaar F.Carrier n) Φ f.val R →
      HasShiftedRationalValue F.canonicalTopologicalData.residueCardinality
        (normalizedAbsoluteValue F.canonicalTopologicalData)
        (generalLinearHaar F.Carrier n) ΦHat (coefficientIota f.val) RDual →
      NormalizedFunctionalEquation F.canonicalTopologicalData.residueCardinality
        1 1 1 c 0 m R RDual

/-- Every actual original continuation is Laurent once the raw monomial
equation is supplied. Rational uniqueness transfers the common clearing to
the continuation specified in the conclusion. -/
theorem SupercuspidalMatrixRationalityData.exists_laurent_value
    {ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V}
    {ω c : ℂˣ} {m : ℤ}
    (hRat : SupercuspidalMatrixRationalityData F ρ ω)
    {ψ : UnitaryAdditiveCharacter F.Carrier} {ν : AdditiveHaarMeasure F.Carrier}
    (hFE : HasMatrixMonomialFunctionalEquation F ψ ν ρ c m)
    (Φ : MatrixTestFunction n F.Carrier) (f : biSmoothMatrixCoefficients ρ)
    {R : RationalFunctions}
    (hR : HasShiftedRationalValue F.canonicalTopologicalData.residueCardinality
      (normalizedAbsoluteValue F.canonicalTopologicalData)
      (generalLinearHaar F.Carrier n) Φ f.val R) :
    ∃ A : LaurentCoefficients, laurentToRatFunc A = R := by
  obtain ⟨R₀, hR₀, hD⟩ := hRat.2.2.1 Φ f
  have huniq := hR₀.2.unique F.canonicalTopologicalData.residueCardinality_gt_one hR.2
  subst R₀
  obtain ⟨ΦHat, _, hpair⟩ := hFE Φ
  obtain ⟨RDual, hRDual, hE⟩ := hRat.2.2.2 ΦHat f
  exact exists_laurent_of_matrix_geometric_clearings F (matrixUniformizer F n).val
    (matrixUniformizer_det_abs_lt_one F n) ω c m hD hE
    (hpair f R RDual hR hRDual)

/-- Fourier surjectivity covers every dual test. Reflecting the raw rational
identity transports the original Laurent value to its actual dual value. -/
theorem SupercuspidalMatrixRationalityData.exists_laurent_iota_value
    {ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V}
    {ω c : ℂˣ} {m : ℤ}
    (hRat : SupercuspidalMatrixRationalityData F ρ ω)
    {ψ : UnitaryAdditiveCharacter F.Carrier} {ν : AdditiveHaarMeasure F.Carrier}
    (hsd : IsSelfDual ψ ν)
    (hFE : HasMatrixMonomialFunctionalEquation F ψ ν ρ c m)
    (Φ : MatrixTestFunction n F.Carrier) (f : biSmoothMatrixCoefficients ρ)
    {RDual : RationalFunctions}
    (hRDual : HasShiftedRationalValue F.canonicalTopologicalData.residueCardinality
      (normalizedAbsoluteValue F.canonicalTopologicalData)
      (generalLinearHaar F.Carrier n) Φ (coefficientIota f.val) RDual) :
    ∃ A : LaurentCoefficients, laurentToRatFunc A = RDual := by
  let T := rectangularFourierEquiv ψ ν (n + 1) (n + 1) hsd
  let Φ₀ := T.symm Φ
  obtain ⟨ΦHat, hFourier, hpair⟩ := hFE Φ₀
  have hΦHat : ΦHat = Φ := by
    apply Hecke.TestFunction.ext
    intro x
    calc
      ΦHat x = rectangularFourierIntegral ψ ν Φ₀ x := (hFourier x).2
      _ = T Φ₀ x := (rectangularFourierEquiv_apply ψ ν _ _ hsd Φ₀ x).symm
      _ = Φ x := by rw [LinearEquiv.apply_symm_apply]
  subst ΦHat
  obtain ⟨R, hR, _⟩ := hRat.2.2.1 Φ₀ f
  obtain ⟨A, hA⟩ := hRat.exists_laurent_value F hFE Φ₀ f hR
  have hid := (hpair f R RDual hR hRDual).rational_identity
    F.canonicalTopologicalData.residueCardinality_gt_one
  let δ := spectralReflectionUnit (Nat.zero_lt_one.trans
    F.canonicalTopologicalData.residueCardinality_gt_one)
  refine ⟨laurentReciprocal δ ((laurentMonomialUnit c m : LaurentCoefficients) * A), ?_⟩
  rw [laurentToRatFunc_reciprocal, map_mul, hA, ← hid, RationalReflection.subst_subst]

/-- Actual irreducible supercuspidality supplies all analytic and generator
assertions once the raw Fourier monomial functional equation is known. -/
theorem normalizedMatrixFunctionalEquationData_of_supercuspidal_of_monomial
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν)
    (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (hρ : GeneralLinear.IsSupercuspidal ρ) (hi : ρ.IsIrreducible)
    (c : ℂˣ) (m : ℤ)
    (hFE : HasMatrixMonomialFunctionalEquation F ψ ν ρ c m) :
    NormalizedMatrixFunctionalEquationData F ψ ν ρ 1 1 c m := by
  let := hi
  let : Nontrivial V := IsSimpleModule.nontrivial
    (MonoidAlgebra ℂ (Langlands.GeneralLinear (n + 1) F.Carrier)) ρ.asModule
  obtain ⟨ω, hRat⟩ := exists_supercuspidalMatrixRationalityData F ρ hρ hi
  refine ⟨⟨hRat.1, ?_, ?_⟩, ⟨hRat.2.1, ?_, ?_⟩, hFE⟩
  · intro Φ f
    obtain ⟨R, hR, _⟩ := hRat.2.2.1 Φ f
    exact ⟨R, hR⟩
  · apply (isNormalizedGenerator_iff _ _).2
    refine ⟨by simp, ?_, ?_⟩
    · rintro R ⟨Φ, f, hR⟩
      simpa using hRat.exists_laurent_value F hFE Φ f hR
    · simpa only [Padic.matrixRationalValues, map_one, inv_one] using
        mem_zetaSpan (one_mem_matrixRationalValues F ρ hρ.1.1)
  · intro Φ f
    obtain ⟨R, hR, _⟩ := hRat.2.2.2 Φ f
    exact ⟨R, hR⟩
  · apply (isNormalizedGenerator_iff _ _).2
    refine ⟨by simp, ?_, ?_⟩
    · rintro R ⟨Φ, f, hR⟩
      simpa using hRat.exists_laurent_iota_value F hsd hFE Φ f hR
    · simpa only [Padic.iotaMatrixRationalValues, map_one, inv_one] using
        mem_zetaSpan (one_mem_iotaMatrixRationalValues F ρ hρ.1.1)

end Langlands.GodementJacquet.Padic
