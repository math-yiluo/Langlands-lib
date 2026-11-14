import Langlands.Representation.Classification.LanglandsData
import Langlands.Representation.Category.Subquotients

/-!
# Langlands quotients as subrepresentations of reversed standard modules: target

Every Langlands head of a multisegment embeds into the product of segment heads taken in an
order in which no later segment precedes an earlier one, and every irreducible subrepresentation
of that product is a Langlands head of the same multisegment. This module states these two
implications; it proves nothing.
-/

namespace Langlands.Classification

universe uF uV

/-- **Target.** Let `d` be a segment-product datum with segment heads as blocks, ordered so
that no later segment precedes an earlier one. Then every Langlands head of the multisegment
of `d` is a subrepresentation of the induced product `d.induced`, and every irreducible
subrepresentation of `d.induced` is a Langlands head of that multisegment. Unproved. -/
def LanglandsSubrepresentationRealization : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ) (d : T.SegmentProductDatum.{max uF uV, uF} n),
      d.HasSegmentHeads →
      (∀ i j, i < j → ¬ (d.segments j).Precedes (d.segments i)) →
      (∀ π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier),
          d.multisegment.IsLanglandsHead π → SmoothRep.IsSubrepresentation π d.induced) ∧
      (∀ π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier),
          π.IsIrreducible → SmoothRep.IsSubrepresentation π d.induced →
            d.multisegment.IsLanglandsHead π)

end Langlands.Classification
