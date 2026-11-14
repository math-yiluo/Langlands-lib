import Langlands.Representation.GodementJacquet.GenericMatrixFunctionalEquationStatement
import Langlands.AllField.Representation.GodementJacquet.AnalyticData
/-!
# Matrix functional-equation data on irreducible Whittaker-type representations

This closed proposition states the generic irreducible specialization of
Godement–Jacquet Theorem 3.3 in the existing plus transpose convention.
It supplies a statement only.
-/

noncomputable section

namespace Langlands.AllField.GodementJacquet
open Langlands.GodementJacquet hiding GenericMatrixFunctionalEquationStatement
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis

universe uF uV

/-- Existence of actual normalized matrix functional-equation data on every
irreducible Whittaker-type representation, with canonical p-adic structures
and the supplied self-dual scalar additive Haar measure. -/
def GenericMatrixFunctionalEquationStatement : Prop :=
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
        letI : MeasurableSpace (Langlands.GeneralLinear (n + 1) F) := borel _
        letI : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
        ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
          (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V),
          RankinSelberg.IsOfWhittakerType n (Whittaker.standardCharacter ψ n) σ →
          Representation.IsIrreducible σ →
          ∃ (P PDual : Polynomial ℂ) (c : ℂˣ) (a : ℤ),
            Langlands.AllField.GodementJacquet.Padic.NormalizedMatrixFunctionalEquationData F ψ ν σ P PDual c a

end Langlands.AllField.GodementJacquet
