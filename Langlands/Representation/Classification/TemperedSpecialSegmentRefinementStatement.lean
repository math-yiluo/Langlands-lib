import Langlands.Representation.Classification.LanglandsData

/-!
# Refining tempered Langlands data into ordered special segments

This proposition records an actual isomorphism of normalized induced objects.
It is an internal refinement interface; no refinement theorem is proved here.
-/

namespace Langlands.Classification

open CategoryTheory

universe uF uV

variable {p : Nat} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Every positive-rank tempered Langlands datum admits a precedence-ordered
special-segment datum with an isomorphic full induced representation. -/
def TemperedSpecialSegmentRefinement : Prop :=
  letI := T.topology
  ∀ (n : Nat), 0 < n →
    ∀ t : T.TemperedLanglandsDatum.{max uF uV, uF} n,
      ∃ d : T.SegmentProductDatum.{max uF uV, uF} n,
        d.IsPrecedenceOrdered ∧ d.HasSegmentHeads ∧
          Nonempty (d.induced ≅ t.standardModule)

end Langlands.Classification
