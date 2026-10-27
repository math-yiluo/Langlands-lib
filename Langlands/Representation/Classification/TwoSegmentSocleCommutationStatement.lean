import Langlands.Representation.Classification.SegmentProductPermutation

/-!
# Commutation of two unlinked segment socles

This proposition asks for an actual isomorphism between the two orders of the
supplied segment-socle blocks. It is an independent two-factor input to
full-product lifting.
-/

namespace Langlands.Classification

open CategoryTheory

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The two actual segment-socle blocks of unlinked segments commute under
normalized product induction. This definition states, but does not prove, the
isomorphism and assumes no order or independent commutation premise. -/
def TwoSegmentSocleCommutation : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (d : T.SegmentProductDatum.{max uF uV, uF} n) (h₂ : d.length = 2),
    d.HasSegmentSocles →
    ¬ (d.segments ⟨0, by omega⟩).IsLinked (d.segments ⟨1, by omega⟩) →
    let σ := d.shape.adjacentSwap 0 (by change 0 + 1 < d.length; omega)
    Nonempty (d.induced ≅ (d.permute σ).induced)

end Langlands.Classification
