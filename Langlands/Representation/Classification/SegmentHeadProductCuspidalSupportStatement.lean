import Langlands.Representation.Classification.SegmentCuspidalContent
import Langlands.Representation.Classification.LanglandsData
import Langlands.Representation.Classification.SupercuspidalSupport

/-!
# Cuspidal support of an irreducible product of segment heads

The product's irreducibility is a premise. The conclusion uses the actual
supercuspidal-support relation and retains every segment-member occurrence.
-/

namespace Langlands.Classification

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- An irreducible induced product of supplied segment heads has the multiset
of all segment-member occurrences as a supercuspidal support. -/
def SegmentHeadProductCuspidalSupport : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (d : T.SegmentProductDatum.{max uF uV, uF} n),
    d.HasSegmentHeads →
    Representation.IsIrreducible d.induced.representation →
    T.IsSupercuspidalSupport d.induced d.multisegment.cuspidalContent

end Langlands.Classification
