import Langlands.Representation.Derivative.MirabolicProductMinusLeftPsi
import Langlands.Representation.Derivative.MirabolicProductMinusLeftPhi
import Langlands.Representation.Derivative.MirabolicProductMinusBoundary
import Langlands.Representation.Derivative.MirabolicProductMinusRightPsi
import Langlands.Representation.Derivative.MirabolicProductMinusRightPhi
import Langlands.Representation.Derivative.MirabolicProductMinusRightBoundary

/-!
# Mixed products and normalized mirabolic minus functors

The six natural minus clauses of BZ77 Proposition 4.13(b,c), including
the two source-rank-one boundaries, for the actual normalized functors.
-/

noncomputable section

namespace Langlands.Derivative

universe uF uV

/-- BZ77 Proposition 4.13(b,c), the exact natural normalized minus
compatibilities and short exact sequence, including both `P_1` boundaries. -/
theorem mirabolicProductMinusCompatibility {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) :
    MirabolicProductMinusCompatibilityStatement.{uF, uV} F T := by
  exact ⟨MirabolicProductMinus.leftPsiCompatibility T,
    MirabolicProductMinus.leftPhiCompatibility T,
    MirabolicProductMinus.leftPhiBoundary T,
    MirabolicProductMinus.rightPsiCompatibility T,
    MirabolicProductMinus.rightPhiShortExact T,
    MirabolicProductMinus.rightPhiBoundary T⟩

end Langlands.Derivative
