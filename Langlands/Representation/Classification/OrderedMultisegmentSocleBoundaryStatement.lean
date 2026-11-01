import Langlands.Representation.Classification.MultisegmentClassificationStatement
import Langlands.Representation.Classification.CuspidalIntegralTwistFreenessStatement

/-!
# Elementary boundary statements for ordered segment-socle products

The rank-zero strong socle, nonzero actual product, and conditional endpoint
separation are grouped as lower inputs to ordered-socle existence.
-/

namespace Langlands.Classification

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Elementary boundary assertions for the actual ordered segment-socle product.
The endpoint clause retains integral-twist freeness explicitly. -/
def OrderedMultisegmentSocleBoundary : Prop :=
  letI := T.topology
  (∀ d : T.SegmentProductDatum.{max uF uV, uF} 0,
    d.IsPrecedenceOrdered → d.HasSegmentSocles →
      d.IsZelevinskySocle d.induced) ∧
  (∀ (n : ℕ) (d : T.SegmentProductDatum.{max uF uV, uF} n),
    d.HasSegmentSocles → Nontrivial d.induced) ∧
  (CuspidalIntegralTwistFreeness.{uF, uV} F T →
    ∀ (r : ℕ) (segments : Fin r → T.Segment.{uV, uF}),
      T.IsPrecedenceOrdered segments →
        ∀ i j : Fin r, i < j →
          (segments j).base ≠ (segments i).last.twist 1)

end Langlands.Classification
