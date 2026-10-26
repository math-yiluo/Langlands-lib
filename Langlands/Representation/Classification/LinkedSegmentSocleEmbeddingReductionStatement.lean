import Langlands.Representation.Classification.SegmentProductPermutation
import Langlands.Representation.Classification.ConstituentRelations

/-!
# Local linked-segment reduction for irreducible socle-product embeddings

An adjacent preceding pair can be swapped or replaced by its union and optional
intersection while retaining an actual embedding into a full normalized product.
-/

namespace Langlands.Classification

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The local embedding reduction of Zelevinsky §6.7, before inversion
minimization. The replacement list retains every outside segment occurrence. -/
def LinkedSegmentSocleEmbeddingReduction : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (d : T.SegmentProductDatum.{max uF uV, uF} n)
    (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)),
    d.HasSegmentSocles →
    IsIrreducibleSubrepresentation d.induced.representation π.representation →
    ∀ (j : ℕ) (h : j + 1 < d.length),
      let Δ' := d.segments ⟨j, by omega⟩
      let Δ := d.segments ⟨j + 1, h⟩
      Δ'.Precedes Δ →
      IsIrreducibleSubrepresentation
          (d.permute (d.shape.adjacentSwap j h)).induced.representation
          π.representation ∨
        ∃ (U : T.Segment.{max uF uV, uF})
          (I : Option (T.Segment.{max uF uV, uF}))
          (e : T.SegmentProductDatum.{max uF uV, uF} n),
          U.support = Δ'.support ∪ Δ.support ∧
          (match I with
            | none => Δ'.support ∩ Δ.support = ∅
            | some J => J.support = Δ'.support ∩ Δ.support) ∧
          List.ofFn e.segments =
            (List.ofFn d.segments).take j ++ [U] ++ I.toList ++
              (List.ofFn d.segments).drop (j + 2) ∧
          e.HasSegmentSocles ∧
          IsIrreducibleSubrepresentation e.induced.representation π.representation

end Langlands.Classification
