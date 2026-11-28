import Langlands.AllFieldBZ.Representation.Classification.OrderedSegmentProducts
import Langlands.AllFieldBZ.Representation.Derivative.Iteration

/-! Derivatives of an actual segment socle over a nonarchimedean local field. -/

namespace Langlands.AllFieldBZ.Classification

open LocalFieldPackage.TopologicalData
open Langlands.AllFieldBZ.Derivative (generalLinearDerivative generalLinearRankCast)

universe uF uV

/-- The only nonzero positive derivative has order equal to the cuspidal
rank. It is a line for a singleton and the initial truncation socle otherwise. -/
def SegmentSocleDerivativeStatement : Prop :=
  ∀ (F : LocalFieldPackage.{uF}) (T : F.TopologicalData),
    letI := T.topology
    ∀ (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
      (Δ : Segment.{uV,uF} T)
      (π : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)),
      T.IsSegmentSocle Δ π →
      (∀ (k : ℕ) (hk : k ≤ Δ.degree), 0 < k → k ≠ Δ.rank →
        Subsingleton ((generalLinearDerivative T ψ Δ.degree k hk).obj π)) ∧
      (∀ h : Δ.rank ≤ Δ.degree, Δ.length = 1 →
        Module.finrank ℂ ((generalLinearDerivative T ψ Δ.degree Δ.rank h).obj π) = 1) ∧
      (∀ (h : Δ.rank ≤ Δ.degree) (h₂ : 2 ≤ Δ.length)
        (he : Δ.degree - Δ.rank = (Δ.length - 1) * Δ.rank),
        T.IsSegmentSocle ⟨Δ.base, Δ.length - 1, by omega⟩
          ((generalLinearRankCast T he).obj
            ((generalLinearDerivative T ψ Δ.degree Δ.rank h).obj π)))

end Langlands.AllFieldBZ.Classification
