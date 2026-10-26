import Langlands.Representation.Classification.Segments
import Langlands.Representation.Exponents.Jacquet

/-!
# Scalar norms of Jacquet exponents of a segment special quotient

This proposition definition states the descending-interval norm formula derived
from Zelevinsky 1980 §§9.1 and 9.5, for every standard block shape and every
generalized exponent of the actual normalized upper Jacquet module.
It assumes the weak segment-quotient relation and proves no assertion.
-/

namespace Langlands.Classification

open GeneralLinear
open scoped BigOperators

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The scalar norm formula for every generalized normalized Jacquet exponent
of an irreducible quotient of the increasing segment induction. The positive
integers `k i` partition the segment into successive descending intervals. -/
def SegmentSpecialJacquetExponentNormFormula : Prop :=
  letI := T.topology
  ∀ (Δ : T.Segment.{max uF uV, uF})
    (A : SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := Δ.rank))
    (ω : F.Carrierˣ →* ℂˣ),
    Δ.base.IsRepresentedBy A →
    HasScalarCharacter A.obj.representation GeneralLinear.scalar ω →
    ∀ (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)),
      T.IsSegmentQuotient Δ π →
      ∀ (B : GeneralLinear.BlockShape Δ.degree)
        (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ),
        T.IsJacquetExponent B π.representation χ →
        ∃ k : Fin B.length → ℕ,
          let K : Fin B.length → ℕ :=
            fun i => ∑ j : Fin B.length with j < i, k j
          (∀ i, 0 < k i) ∧
          (∀ i, B.size i = Δ.rank * k i) ∧
          (∑ i, k i) = Δ.length ∧
          ∀ a : Fin B.length → F.Carrierˣ,
            ‖(χ a : ℂ)‖ =
              ∏ i, (‖(ω (a i) : ℂ)‖ ^ k i *
                T.normalizedAbs (a i : F.Carrier) ^
                  ((Δ.rank : ℝ) * (k i : ℝ) *
                    (((2 * (Δ.length : ℝ) - (k i : ℝ) - 1) / 2) - (K i : ℝ))))

end Langlands.Classification
