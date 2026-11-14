import Langlands.Representation.GodementJacquet.TateMatrixFunctionalEquationStatement
import Langlands.AllField.Representation.GodementJacquet.AnalyticData
/-!
# Tate matrix functional-equation base in rank one

This closed proposition records a genuine analytic base case of
Godement–Jacquet Theorem 3.3. It supplies a statement only.
-/

noncomputable section

namespace Langlands.AllField.GodementJacquet
open Langlands.GodementJacquet hiding TateMatrixFunctionalEquationStatement
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis

universe uF uV

/-- Full normalized matrix functional-equation data for every admissible
irreducible representation of GL₁, with the supplied self-dual measure. -/
def TateMatrixFunctionalEquationStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F],
    letI : MeasurableSpace F := borel _
    letI : BorelSpace F := ⟨rfl⟩
    haveI : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
    haveI : TotallyDisconnectedSpace F := by
      let : NonarchimedeanRing F := by
        convert! ValuativeRel.nonarchimedeanRing F
        exact Valuation.toTopologicalSpace_eq _
      infer_instance
    ∀ (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F),
      IsSelfDual ψ ν →
      letI : MeasurableSpace (Langlands.GeneralLinear 1 F) := borel _
      letI : BorelSpace (Langlands.GeneralLinear 1 F) := ⟨rfl⟩
      ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
        (σ : Representation ℂ (Langlands.GeneralLinear 1 F) V),
        IsAdmissible σ → Representation.IsIrreducible σ →
        ∃ (P PDual : Polynomial ℂ) (c : ℂˣ) (a : ℤ),
          Langlands.AllField.GodementJacquet.Padic.NormalizedMatrixFunctionalEquationData (n := 0) F ψ ν σ P PDual c a

end Langlands.AllField.GodementJacquet
