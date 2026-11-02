import Langlands.Representation.Classification.SegmentFullJacquetProof
import Langlands.Representation.Classification.TwoSegmentShufflePieces
import Langlands.Representation.Classification.TwoSegmentShuffleAssembly

/-!
# Cuspidal Jacquet modules of a product of two segment socles on one line

Zelevinsky 1980, 1.6 and 3.1, for two segment socles on one cuspidal line,
assembled from the shuffle filtration of `TwoSegmentShuffleAssembly`, the
surviving-piece computation of `TwoSegmentShufflePieces` and Ze80 3.1
(`segmentFullJacquetFormula`).
-/

namespace Langlands.Classification

namespace TwoSegmentShuffle

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Ze80 3.1 for segment subrepresentations gives the surviving-piece interface
of the shuffle assembly, through the pointwise `surviving_piece_equiv`. -/
theorem survivingPieceEquiv_of_segmentSubrepresentationFullJacquet
    (h31 : SegmentSubrepresentationFullJacquet.{uF, uV} F T) :
    SurvivingPieceEquiv.{uF, uV} F T :=
  fun _ A a₀ a₁ _ _ d h₂ hA hsoc hb₀ _ hb₁ _ h₀ h₁ w S R hS hR hdiv =>
    surviving_piece_equiv F T h31 A hA a₀ a₁ d h₂ hsoc hb₀ hb₁ h₀ h₁ w S R hS hR hdiv

end TwoSegmentShuffle

universe uF uV uW

/-- Zelevinsky 1980, 1.6 and 3.1, for two segment socles on one cuspidal line:
the normalized Jacquet module of `⟨Δ₀⟩ × ⟨Δ₁⟩` along `(r, …, r)` has composition
length `(m₀+m₁).choose m₀`, and each irreducible `τ` occurs as often as there are
shuffles whose tensor is equivalent to `τ`. -/
theorem twoSegmentSocleShuffleJacquet
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    TwoSegmentSocleShuffleJacquet.{uF, uV, uW} F T :=
  TwoSegmentShuffle.twoSegmentSocleShuffleJacquet_of_survivingPieceEquiv F T
    (TwoSegmentShuffle.survivingPieceEquiv_of_segmentSubrepresentationFullJacquet F T
      (segmentFullJacquetFormula.{uF, uV} F T).1)

end Langlands.Classification
