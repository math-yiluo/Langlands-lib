import Langlands.Representation.GodementJacquet.FunctionalEquationTransportStatement
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonTransport

/-!
# Transport of full normalized matrix functional-equation data

The existing actual-data equivalence theorem proves the closed statement.
Its canonical p-adic specialization retains the supplied Fourier measure.
-/

noncomputable section

namespace Langlands.GodementJacquet

open MeasureTheory HarmonicAnalysis RankinSelberg

universe uF uV uW

/-- Closed transport theorem with three independent carrier universes. -/
theorem normalizedMatrixFunctionalEquationTransport :
    NormalizedMatrixFunctionalEquationTransportStatement.{uF,uV,uW} := by
  intro F _ _ _ n _ V _ _ W _ _ q ψ ν abv μ σ τ e P PDual c m
  exact normalizedMatrixFunctionalEquationData_equiv e

namespace Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance matrixFETransportTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance matrixFETransportValuative : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance matrixFETransportLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance matrixFETransportMeasurable : MeasurableSpace F.Carrier := borel _
local instance matrixFETransportBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance matrixFETransportGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  borel _
local instance matrixFETransportGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩

variable {n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V}
  {τ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W}

/-- Canonical p-adic specialization retaining the supplied Fourier measure. -/
theorem normalizedMatrixFunctionalEquationData_equiv
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (e : σ.Equiv τ) (P PDual : Polynomial ℂ) (c : ℂˣ) (m : ℤ) :
    NormalizedMatrixFunctionalEquationData F ψ ν σ P PDual c m ↔
      NormalizedMatrixFunctionalEquationData F ψ ν τ P PDual c m :=
  GodementJacquet.normalizedMatrixFunctionalEquationData_equiv
    (q := F.canonicalTopologicalData.residueCardinality) (ψ := ψ) (ν := ν)
    (abv := normalizedAbsoluteValue F.canonicalTopologicalData)
    (μ := generalLinearHaar F.Carrier n) e

end Padic

end Langlands.GodementJacquet
