import Langlands.Group.GL.LowerBlockQuotientGeometryStatement
import Langlands.AllField.Group.GL.PadicSupplement
/-!
# Geometry of the actual lower-block quotient chart

The open embedding, measurability and conullness conclusions extracted from
`LowerBlockQuotientDisintegrationStatement`, with the same canonical structures
and actual chart. This module states the geometry proposition; it proves none
of these conclusions.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding LowerBlockQuotientGeometryStatement
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.GeneralLinear
open Langlands.QuotientIntegration

universe uF

/-- The actual lower-block chart on the left unipotent quotient is an open
embedding, is measurable, and has conull range for every compatible measure
on the large quotient. The ranks are `a = n + 1` and `d = k + 1`. -/
def LowerBlockQuotientGeometryStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (n k : ℕ),
    letI := borel F
    letI : BorelSpace F := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (n + 1) F)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F)
    letI : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
    letI := borel (LeftQuotient (upperUnipotent (n + 1) F))
    letI : BorelSpace (LeftQuotient (upperUnipotent (n + 1) F)) := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (n + 1 + k + 1) F)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1 + k + 1) F) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1 + k + 1) F)
    letI : BorelSpace (upperUnipotent (n + 1 + k + 1) F) := ⟨rfl⟩
    letI := borel (LeftQuotient (upperUnipotent (n + 1 + k + 1) F))
    letI : BorelSpace (LeftQuotient (upperUnipotent (n + 1 + k + 1) F)) := ⟨rfl⟩
    letI := borel (lowerTriangularSubgroup (k + 1) F)
    letI : BorelSpace (lowerTriangularSubgroup (k + 1) F) := ⟨rfl⟩
    let chart : LowerBlockQuotientParameters (n + 1) (k + 1) F →
        LeftQuotient (upperUnipotent (n + 1 + k + 1) F) :=
      lowerBlockQuotientChart
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F (n + 1 + k))],
    ∀ (μ : Measure (LeftQuotient (upperUnipotent (n + 1 + k + 1) F))),
      IsCompatible (upperUnipotent (n + 1 + k + 1) F)
        (generalLinearHaar F (n + 1 + k)) (unipotentHaar F (n + 1 + k)) μ →
      Topology.IsOpenEmbedding chart ∧ Measurable chart ∧ μ (Set.range chart)ᶜ = 0

end Langlands.AllField.RankinSelberg
