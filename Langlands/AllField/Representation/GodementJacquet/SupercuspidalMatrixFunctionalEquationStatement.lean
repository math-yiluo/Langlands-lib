import Langlands.Representation.GodementJacquet.SupercuspidalMatrixFunctionalEquationStatement
import Langlands.AllField.Representation.GodementJacquet.AnalyticData
/-!
# Supercuspidal matrix functional-equation base

This closed proposition records a genuine analytic base case of
Godement–Jacquet Theorem 3.3. It supplies a statement only.
-/

noncomputable section

namespace Langlands.AllField.GodementJacquet
open Langlands.GodementJacquet hiding SupercuspidalMatrixFunctionalEquationStatement
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis

universe uF uV

/-- Full normalized matrix functional-equation data with both Euler
denominators equal to one for every irreducible supercuspidal of rank at least two. -/
def SupercuspidalMatrixFunctionalEquationStatement : Prop :=
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
      ∀ n : ℕ,
        letI : MeasurableSpace (Langlands.GeneralLinear (n + 2) F) := borel _
        letI : BorelSpace (Langlands.GeneralLinear (n + 2) F) := ⟨rfl⟩
        ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
          (σ : Representation ℂ (Langlands.GeneralLinear (n + 2) F) V),
          GeneralLinear.IsSupercuspidal σ → Representation.IsIrreducible σ →
          ∃ (c : ℂˣ) (a : ℤ),
            Langlands.AllField.GodementJacquet.Padic.NormalizedMatrixFunctionalEquationData (n := n + 1)
              F ψ ν σ 1 1 c a

end Langlands.AllField.GodementJacquet
