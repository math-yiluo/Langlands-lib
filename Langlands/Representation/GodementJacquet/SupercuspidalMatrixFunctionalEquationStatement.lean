import Langlands.Representation.GodementJacquet.AnalyticData
import Langlands.LocalField.Topology
import Langlands.Representation.Classification.Supercuspidal

/-!
# Supercuspidal matrix functional-equation base

This closed proposition records a genuine analytic base case of
Godement–Jacquet Theorem 3.3. It supplies a statement only.
-/

noncomputable section

namespace Langlands.GodementJacquet

open MeasureTheory HarmonicAnalysis

universe uF uV

/-- Full normalized matrix functional-equation data with both Euler
denominators equal to one for every irreducible supercuspidal of rank at least two. -/
def SupercuspidalMatrixFunctionalEquationStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p),
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    letI : MeasurableSpace F.Carrier := borel _
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    haveI : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
    haveI : TotallyDisconnectedSpace F.Carrier := by
      let : NonarchimedeanRing F.Carrier := by
        convert! ValuativeRel.nonarchimedeanRing F.Carrier
        exact Valuation.toTopologicalSpace_eq _
      infer_instance
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier),
      IsSelfDual ψ ν →
      ∀ n : ℕ,
        letI : MeasurableSpace (Langlands.GeneralLinear (n + 2) F.Carrier) := borel _
        letI : BorelSpace (Langlands.GeneralLinear (n + 2) F.Carrier) := ⟨rfl⟩
        ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
          (σ : Representation ℂ (Langlands.GeneralLinear (n + 2) F.Carrier) V),
          GeneralLinear.IsSupercuspidal σ → Representation.IsIrreducible σ →
          ∃ (c : ℂˣ) (a : ℤ),
            Padic.NormalizedMatrixFunctionalEquationData (n := n + 1)
              F ψ ν σ 1 1 c a

end Langlands.GodementJacquet
