import Langlands.Representation.Classification.Segments
import Langlands.Representation.Induction.BlockFactors
import Langlands.Representation.Jacquet.Parabolic

/-!
# Ordered Jacquet factors of a weak segment quotient

This proposition definition states the object-level factorization needed to
extend the special-head two-block formula to arbitrary ordered block shapes and
every weak quotient of an increasing segment induction. It is an internal
consequence sought from Zelevinsky 1980 §§9.1 and 9.5 and normalized upper
Jacquet transitivity. This file proves no factorization.
-/

namespace Langlands.Classification

open GeneralLinear
open scoped BigOperators

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- For every actual weak segment quotient and ordered block shape, its actual
normalized upper Jacquet module is zero or is equivalent to a tensor of weak
quotients for successive descending subsegments. The factors have the actual
block degrees; `hdeg` transports them to the degrees of their segments. -/
def SegmentQuotientJacquetFactors : Prop :=
  letI := T.topology
  ∀ (Δ : T.Segment.{max uF uV, uF})
    (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)),
    T.IsSegmentQuotient Δ π →
    ∀ B : BlockShape Δ.degree,
      Subsingleton (B.JacquetModule π.representation) ∨
        ∃ (k : Fin B.length → ℕ)
          (Γ : Fin B.length → T.Segment.{max uF uV, uF})
          (hdeg : ∀ i, (Γ i).degree = B.size i)
          (σ : ∀ i, SmoothRep.{0, uF, max uF uV} ℂ
            (GeneralLinear (B.size i) F.Carrier)),
          (∀ i, 0 < k i) ∧
          (∀ i, B.size i = Δ.rank * k i) ∧
          (∑ i, k i) = Δ.length ∧
          (∀ i, (Γ i).length = k i) ∧
          (∀ i, (Γ i).base =
            Δ.member (Δ.length - (∑ j : Fin B.length with j < i, k j) - k i)) ∧
          (∀ i, T.IsSegmentQuotient (Γ i) ((hdeg i).symm ▸ σ i)) ∧
          Nonempty ((T.normalizedJacquet B π.representation).Equiv
            (B.blockTensor (fun i => (σ i).representation)))

end Langlands.Classification
