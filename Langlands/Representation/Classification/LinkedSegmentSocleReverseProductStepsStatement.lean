import Langlands.Representation.Classification.LanglandsData
import Langlands.Representation.Classification.SegmentReplacementInversions
import Langlands.Representation.Filtration.ObjectDefinitions

/-!
# Steps (1) and (2) of Zelevinsky's Proposition 4.6

Two Prop-valued statements, both unproved here: the juxtaposed case of
Zelevinsky 1980, Proposition 4.6, and the nonzero intertwining map
`⟨Δ⟩ × ⟨Δ'⟩ → ⟨Δ ∪ Δ'⟩ × ⟨Δ ∩ Δ'⟩` for every precedence pair. They are
steps of the proof of `LinkedSegmentSocleReverseProductStructure`.
-/

namespace Langlands.Classification

open CategoryTheory

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Ze80 Proposition 4.6, step (1): the full conclusion of
`LinkedSegmentSocleReverseProductStructure` for a socle datum `⟨Δ⟩ × ⟨Δ'⟩`
whose second segment `Δ'` precedes and is juxtaposed with the first `Δ`. -/
def JuxtaposedSegmentSocleReverseProductStructure : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (d : T.SegmentProductDatum.{uV, uF} n) (h₂ : d.length = 2),
    d.HasSegmentSocles →
    (d.segments ⟨1, by omega⟩).Precedes (d.segments ⟨0, by omega⟩) →
    (d.segments ⟨1, by omega⟩).IsJuxtaposed (d.segments ⟨0, by omega⟩) →
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

/-- Ze80 Proposition 4.6, step (2): if `Δ'` precedes `Δ`, then
`Hom(⟨Δ⟩ × ⟨Δ'⟩, ω) ≠ 0` for every socle datum `e` of the union followed by
the optional intersection, where `ω = e.induced`. -/
def LinkedSegmentSocleReverseProductQuotientHom : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (d : T.SegmentProductDatum.{uV, uF} n) (h₂ : d.length = 2),
    d.HasSegmentSocles →
    (d.segments ⟨1, by omega⟩).Precedes (d.segments ⟨0, by omega⟩) →
    ∀ (U : T.Segment.{uV, uF}) (I : Option (T.Segment.{uV, uF}))
      (e : T.SegmentProductDatum.{uV, uF} n),
      (d.segments ⟨0, by omega⟩).IsUnionIntersectionReplacement
          (d.segments ⟨1, by omega⟩) U I →
        List.ofFn e.segments = U :: I.toList →
        e.HasSegmentSocles →
        ∃ f : d.induced.representation.IntertwiningMap e.induced.representation, f ≠ 0

end Langlands.Classification
