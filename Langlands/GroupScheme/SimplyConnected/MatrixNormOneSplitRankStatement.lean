import Langlands.GroupScheme.CentralSimpleNormOne
import Langlands.GroupScheme.Rational.SplitTorus

/-!
# Split rank of special linear groups over division algebras

This module states the split-rank formula for the actual reduced-norm-one
group of a matrix algebra over a finite-dimensional central division algebra.
It supplies no proof.
-/

noncomputable section

universe u

namespace Langlands.GroupScheme.CentralSimpleUnits

/-- The split rank of `SL_m(D)` is `m - 1` for a finite-dimensional central
division algebra `D` over any field. The positive size includes `m = 1`. -/
def MatrixNormOneSplitRankStatement : Prop :=
  ∀ (K D : Type u) [Field K] [DivisionRing D] [Algebra K D]
    [FiniteDimensional K D] [Algebra.IsCentral K D] (m : ℕ) [NeZero m],
    splitRank (normOne K (Matrix (Fin m) (Fin m) D)) = ((m - 1 : ℕ) : ℕ∞)

end Langlands.GroupScheme.CentralSimpleUnits
