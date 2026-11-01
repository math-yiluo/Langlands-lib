import Langlands.Representation.GodementJacquet.AnalyticData
import Langlands.LocalField.Topology

/-!
# Tate matrix functional-equation base in rank one

This closed proposition records a genuine analytic base case of
Godement–Jacquet Theorem 3.3. It supplies a statement only.
-/

noncomputable section

namespace Langlands.GodementJacquet

open MeasureTheory HarmonicAnalysis

universe uF uV

/-- Full normalized matrix functional-equation data for every admissible
irreducible representation of GL₁, with the supplied self-dual measure. -/
def TateMatrixFunctionalEquationStatement : Prop :=
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
      letI : MeasurableSpace (Langlands.GeneralLinear 1 F.Carrier) := borel _
      letI : BorelSpace (Langlands.GeneralLinear 1 F.Carrier) := ⟨rfl⟩
      ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
        (σ : Representation ℂ (Langlands.GeneralLinear 1 F.Carrier) V),
        IsAdmissible σ → Representation.IsIrreducible σ →
        ∃ (P PDual : Polynomial ℂ) (c : ℂˣ) (a : ℤ),
          Padic.NormalizedMatrixFunctionalEquationData (n := 0) F ψ ν σ P PDual c a

end Langlands.GodementJacquet
