import Langlands.Representation.Derivative.Homogeneity
import Langlands.Representation.Classification.LanglandsData

/-!
# Homogeneity of endpoint-separated segment-socle products

This is the full endpoint condition of Zelevinsky 1980, Theorem 6.2,
on every actual supplied positive-rank product. No proof is supplied.
-/

noncomputable section

namespace Langlands.Classification

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Every actual segment-socle product whose later beginnings avoid the
one-step twists of earlier ends has homogeneous mirabolic restriction. -/
def SegmentSocleProductHomogeneity : Prop :=
  letI := T.topology
  ∀ (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (N : ℕ) (d : T.SegmentProductDatum.{uV, uF} (N + 1)),
    d.HasSegmentSocles →
      (∀ i j : Fin d.length, i < j →
        (d.segments j).base ≠ ((d.segments i).last).twist 1) →
      Derivative.IsGeneralLinearHomogeneous T ψ d.induced

end Langlands.Classification
