import Langlands.Representation.GodementJacquet.FunctionalEquationDescentProof
import Langlands.Representation.GodementJacquet.SubquotientCoefficientInclusionProof
import Langlands.Representation.GodementJacquet.MatrixUnitValueProof

/-! # Normalized matrix equation data on actual p-adic subquotients -/

noncomputable section

namespace Langlands.GodementJacquet.Padic

open HarmonicAnalysis RankinSelberg MeasureTheory

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance subquotientDescentTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance subquotientDescentValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance subquotientDescentLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance subquotientDescentT2Space : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2
local instance subquotientDescentTotallyDisconnectedSpace :
    TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance subquotientDescentMeasurableSpace : MeasurableSpace F.Carrier := borel _
local instance subquotientDescentBorelSpace : BorelSpace F.Carrier := ⟨rfl⟩
local instance subquotientDescentGLMeasurableSpace (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  borel _
local instance subquotientDescentGLBorelSpace (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩

variable {n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W] [Nontrivial W]
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V}
  {τ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W}

/-- A nonzero smooth coefficient subfamily inherits full normalized matrix data,
with new generators, unit and exponent. -/
theorem normalizedMatrixFunctionalEquationData_of_coefficient_inclusion
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (hτ : IsSmooth τ)
    (hincl : biSmoothMatrixCoefficients τ ≤ biSmoothMatrixCoefficients σ)
    {P PDual : Polynomial ℂ} {c : ℂˣ} {m : ℤ}
    (hdata : NormalizedMatrixFunctionalEquationData F ψ ν σ P PDual c m) :
    ∃ (Q QDual : Polynomial ℂ) (d : ℂˣ) (a : ℤ),
      NormalizedMatrixFunctionalEquationData F ψ ν τ Q QDual d a := by
  obtain ⟨hone, honeDual⟩ := matrixUnitValue p F n W τ hτ
  exact GodementJacquet.normalizedMatrixFunctionalEquationDescent
    F.Carrier n V W F.canonicalTopologicalData.residueCardinality ψ ν
    (normalizedAbsoluteValue F.canonicalTopologicalData) (generalLinearHaar F.Carrier n)
    σ τ F.canonicalTopologicalData.residueCardinality_gt_one hsd hincl
    (mem_zetaSpan hone) (mem_zetaSpan honeDual) P PDual c m hdata

/-- Every nonzero actual subquotient of a smooth representation inherits its
full normalized matrix equation data for the supplied self-dual Fourier measure. -/
theorem normalizedMatrixFunctionalEquationData_of_subquotient
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (hσ : IsSmooth σ)
    (A : Subrepresentation σ) (f : A.toRepresentation.IntertwiningMap τ)
    (hf : Function.Surjective f)
    {P PDual : Polynomial ℂ} {c : ℂˣ} {m : ℤ}
    (hdata : NormalizedMatrixFunctionalEquationData F ψ ν σ P PDual c m) :
    ∃ (Q QDual : Polynomial ℂ) (d : ℂˣ) (a : ℤ),
      NormalizedMatrixFunctionalEquationData F ψ ν τ Q QDual d a := by
  let i : A.toRepresentation.IntertwiningMap σ :=
    { toLinearMap := A.toSubmodule.subtype
      isIntertwining' _ := by ext; rfl }
  have hA : IsSmooth A.toRepresentation :=
    isSmooth_of_injective i Subtype.val_injective hσ
  have hτ : IsSmooth τ := isSmooth_of_surjective f hf hA
  exact normalizedMatrixFunctionalEquationData_of_coefficient_inclusion F ψ ν hsd hτ
    (subquotientCoefficientInclusion p F n V W σ τ hσ A f hf) hdata

end Langlands.GodementJacquet.Padic
