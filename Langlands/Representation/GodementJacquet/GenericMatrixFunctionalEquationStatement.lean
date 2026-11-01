import Langlands.Representation.GodementJacquet.AnalyticData
import Langlands.LocalField.Topology

/-!
# Matrix functional-equation data on irreducible Whittaker-type representations

This closed proposition states the generic irreducible specialization of
Godement–Jacquet Theorem 3.3 in the existing plus transpose convention.
It supplies a statement only.
-/

noncomputable section

namespace Langlands.GodementJacquet

open MeasureTheory HarmonicAnalysis

universe uF uV

/-- Existence of actual normalized matrix functional-equation data on every
irreducible Whittaker-type representation, with canonical p-adic structures
and the supplied self-dual scalar additive Haar measure. -/
def GenericMatrixFunctionalEquationStatement : Prop :=
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
        letI : MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
        letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
        ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
          (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V),
          RankinSelberg.IsOfWhittakerType n (Whittaker.standardCharacter ψ n) σ →
          Representation.IsIrreducible σ →
          ∃ (P PDual : Polynomial ℂ) (c : ℂˣ) (a : ℤ),
            Padic.NormalizedMatrixFunctionalEquationData F ψ ν σ P PDual c a

end Langlands.GodementJacquet
