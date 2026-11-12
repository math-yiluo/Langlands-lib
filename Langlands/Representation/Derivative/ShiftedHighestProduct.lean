import Langlands.Representation.Derivative.HighestProduct
import Langlands.Representation.Induction.BinaryRealTwist

/-! The actual shifted highest-product comparison, with all rank boundaries. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.Derivative.HighestProduct

open CategoryTheory

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData)

private def segmentFactorRankCastIso {a b : ℕ} (h : a = b)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
    (t : ℝ) :
    letI := T.topology
    T.segmentFactor ((generalLinearRankCast T h).obj A) t ≅
      (generalLinearRankCast T h).obj (T.segmentFactor A t) := by
  subst b
  exact Iso.refl _

variable (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
  {a b : ℕ}
  (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
  (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier))
  (r s : ℕ) (hr : r ≤ a) (hs : s ≤ b)
  (hA : letI := T.topology
    ∀ j (hj : j ≤ a), r < j →
      Subsingleton ((generalLinearDerivative T ψ a j hj).obj A))
  (hB : letI := T.topology
    ∀ j (hj : j ≤ b), s < j →
      Subsingleton ((generalLinearDerivative T ψ b j hj).obj B))

/-- At the sum of factor derivative bounds, the actual shifted derivative of
the binary product is the rank-transported binary product of the two shifted
derivatives. Zero ranks and zero derivatives are allowed. -/
def shiftedHighestProductIso (hrs : r + s ≤ a + b) :
    letI := T.topology
    T.segmentFactor
        ((generalLinearDerivative T ψ (a + b) (r + s) hrs).obj
          ((T.binaryNormalizedProductFunctor a b).obj (A, B))) (1 / 2) ≅
      (generalLinearRankCast T (by omega : (a - r) + (b - s) = (a + b) - (r + s))).obj
        ((T.binaryNormalizedProductFunctor (a - r) (b - s)).obj
          (T.segmentFactor ((generalLinearDerivative T ψ a r hr).obj A) (1 / 2),
            T.segmentFactor ((generalLinearDerivative T ψ b s hs).obj B) (1 / 2))) := by
  let := T.topology
  let h : (a - r) + (b - s) = (a + b) - (r + s) := by omega
  let P := (T.binaryNormalizedProductFunctor (a - r) (b - s)).obj
    ((generalLinearDerivative T ψ a r hr).obj A,
      (generalLinearDerivative T ψ b s hs).obj B)
  exact SmoothRep.twistIso
      (T.determinantPowerCharacter ((a + b) - (r + s)) (1 / 2))
      (T.isOpen_ker_determinantPowerCharacter ((a + b) - (r + s)) (1 / 2))
      (highestProductIso T ψ A B r s hr hs hA hB hrs) ≪≫
    segmentFactorRankCastIso T h P (1 / 2) ≪≫
    (generalLinearRankCast T h).mapIso
      (T.binaryNormalizedProductRealTwistIso
        ((generalLinearDerivative T ψ a r hr).obj A)
        ((generalLinearDerivative T ψ b s hs).obj B) (1 / 2))

end Langlands.Derivative.HighestProduct
