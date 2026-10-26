import Langlands.Representation.Classification.SegmentProductPermutation
import Langlands.Representation.Classification.SegmentReplacementInversions
import Langlands.Representation.Filtration.ObjectDefinitions

/-!
# Gluing of the forward product of two linked segment socles

For two linked segments `Δ'` preceding `Δ`, the forward product `⟨Δ'⟩ × ⟨Δ⟩`
has an actual two-step filtration. One graded piece is isomorphic to the
product of actual segment socles of the union and the nonempty intersection;
the other embeds into the reverse product `⟨Δ⟩ × ⟨Δ'⟩`. The orientation of the
filtration is not prescribed. This is a two-factor input to full-product lifting.
-/

namespace Langlands.Classification

open CategoryTheory

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The forward product of the actual socle blocks of two segments, the first
preceding the second, is glued from the union/intersection socle product and a
representation embedding into the reverse product. This definition states, but
does not prove, the gluing; it assumes no order, finite length or independent
gluing premise. -/
def LinkedSegmentSocleGluing : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (d : T.SegmentProductDatum.{max uF uV, uF} n) (h₂ : d.length = 2),
    d.HasSegmentSocles →
    (d.segments ⟨0, by omega⟩).Precedes (d.segments ⟨1, by omega⟩) →
    let σ := d.shape.adjacentSwap 0 (by change 0 + 1 < d.length; omega)
    ∃ (U : T.Segment.{max uF uV, uF}) (I : Option (T.Segment.{max uF uV, uF}))
      (e : T.SegmentProductDatum.{max uF uV, uF} n),
      (d.segments ⟨0, by omega⟩).IsUnionIntersectionReplacement
          (d.segments ⟨1, by omega⟩) U I ∧
        List.ofFn e.segments = U :: I.toList ∧
        e.HasSegmentSocles ∧
        ∃ (s : ObjectRepFiltration (Rep.of d.induced.representation) 2) (i j : Fin 2),
          i ≠ j ∧
            Nonempty ((s.gradedRepresentation i).ρ.Equiv e.induced.representation) ∧
            ∃ f : (s.gradedRepresentation j).ρ.IntertwiningMap
                (d.permute σ).induced.representation,
              Function.Injective f

end Langlands.Classification
