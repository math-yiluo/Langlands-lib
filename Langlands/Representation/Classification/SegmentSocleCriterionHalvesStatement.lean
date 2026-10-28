import Langlands.Representation.Classification.LanglandsData
import Langlands.Representation.Classification.SegmentReplacementInversions
import Langlands.Representation.Filtration.ObjectDefinitions

/-!
# The two halves of Zelevinsky's segment socle irreducibility criterion

Proposition definitions for Zelevinsky 1980, Theorem 4.2, implication
(2)⇒(1), for the full Proposition 4.6 and for the reducibility of a product of
two linked segment socles in either order. The blocks are the supplied segment
socles `⟨Δ⟩` of the increasing cuspidal inductions. Nothing is proved here.
-/

namespace Langlands.Classification

open CategoryTheory

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Ze80 Theorem 4.2, implication (2)⇒(1): a product of segment socles whose
segments are pairwise nonlinked is irreducible. The ordering is unrestricted. -/
def UnlinkedSegmentSocleProductIrreducible : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (d : T.SegmentProductDatum.{uV, uF} (n + 1)),
    d.HasSegmentSocles → d.multisegment.IsUnlinked →
      Representation.IsIrreducible d.induced.representation

/-- Ze80 Proposition 4.6: if `Δ' = d.segments 1` precedes `Δ = d.segments 0`,
then `⟨Δ⟩ × ⟨Δ'⟩` has a unique irreducible subrepresentation `ω₀`, the
quotient by `ω₀` is isomorphic to the irreducible product
`ω = ⟨Δ ∪ Δ'⟩ × ⟨Δ ∩ Δ'⟩` (the intersection omitted when empty), and
`ω₀` is not isomorphic to `ω`. -/
def LinkedSegmentSocleReverseProductStructure : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (d : T.SegmentProductDatum.{uV, uF} n) (h₂ : d.length = 2),
    d.HasSegmentSocles →
    (d.segments ⟨1, by omega⟩).Precedes (d.segments ⟨0, by omega⟩) →
    ∃ (U : T.Segment.{uV, uF}) (I : Option (T.Segment.{uV, uF}))
      (e : T.SegmentProductDatum.{uV, uF} n),
      (d.segments ⟨0, by omega⟩).IsUnionIntersectionReplacement
          (d.segments ⟨1, by omega⟩) U I ∧
        List.ofFn e.segments = U :: I.toList ∧
        e.HasSegmentSocles ∧
        Representation.IsIrreducible e.induced.representation ∧
        ∃ s : ObjectRepFiltration (Rep.of d.induced.representation) 2,
          s.HasSimpleFactors ∧
            Nonempty ((s.gradedRepresentation 1).ρ.Equiv e.induced.representation) ∧
            ¬ Nonempty ((s.gradedRepresentation 0).ρ.Equiv e.induced.representation) ∧
            ∀ K : Subrepresentation d.induced.representation,
              Representation.IsIrreducible K.toRepresentation →
                K = s.subrepresentation 1

/-- The product of the socles of two linked segments is reducible, in either
order: no precedence premise is imposed. -/
def LinkedSegmentSoclePairReducible : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (d : T.SegmentProductDatum.{uV, uF} n) (h₂ : d.length = 2),
    d.HasSegmentSocles →
    (d.segments ⟨0, by omega⟩).IsLinked (d.segments ⟨1, by omega⟩) →
      ¬ Representation.IsIrreducible d.induced.representation

end Langlands.Classification
