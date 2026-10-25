import Langlands.Representation.Classification.Segments
import Langlands.Representation.Classification.Tempered

/-!
# Nonlinkage of square-integrable special segments

This proposition definition records the nonlinkage observation following
Kudla 1994, Proposition 2.2.1, printed p.373. It uses the actual special-head
relation and analytic square-integrability, without a chosen centered
presentation or a classification hypothesis. No proof is asserted.
-/

namespace Langlands.Classification

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Two segments whose special heads are analytically square-integrable are
unlinked. Their degrees may differ, and the two segments may coincide. -/
def SquareIntegrableSegmentNonlinkage : Prop :=
  letI := T.topology
  ∀ (Δ Δ' : T.Segment.{max uF uV, uF})
    (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (π' : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ'.degree F.Carrier)),
    T.IsSegmentHead Δ π → T.IsSegmentHead Δ' π' →
      T.IsSquareIntegrable π.representation →
        T.IsSquareIntegrable π'.representation → ¬ Δ.IsLinked Δ'

end Langlands.Classification
