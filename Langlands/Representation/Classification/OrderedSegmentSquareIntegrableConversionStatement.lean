import Langlands.Representation.Classification.LanglandsData

/-!
# Ordered segment products and square-integrable Langlands data

A proposition stating conversion by reordering actual segment-head blocks,
with an isomorphism of the full normalized induced products. The analytic
identification of the blocks and the permitted reordering are not proved here.
-/

namespace Langlands.Classification

open CategoryTheory

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- A precedence-ordered product of segment heads is isomorphic to the product
of square-integrable Langlands data with the same blocks up to permutation,
rank transport, and actual isomorphism. No head of the full product is assumed. -/
def OrderedSegmentSquareIntegrableConversion : Prop :=
  letI := T.topology
  ∀ (n : ℕ), 0 < n →
    ∀ d : T.SegmentProductDatum.{max uF uV, uF} n,
      d.IsPrecedenceOrdered → d.HasSegmentHeads →
        ∃ e : T.SquareIntegrableLanglandsDatum.{max uF uV, uF} n,
          Nonempty (d.induced ≅ e.induced) ∧
            ∃ σ : Fin d.length ≃ Fin e.shape.length,
              ∀ i, ∃ h : (d.segments i).degree = e.shape.size (σ i),
                Nonempty ((h ▸ d.blocks i) ≅ e.blocks (σ i))

end Langlands.Classification
