import Langlands.Geometry.Analytic.RationalLocalization.Definitions

/-! # Product construction for rational intersections -/

noncomputable section

universe u

namespace Langlands.Analytic.RationalIntersection

open StrictTateAlgebra PresentedStrictAffinoidAlgebra
open scoped Pointwise

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (P : PresentedStrictAffinoidAlgebra K)
  (m n : ℕ) (g h : P) (f : Fin m → P) (k : Fin n → P)

/-- Include each original denominator, then take all pairwise products.
Including the mixed numerator products preserves the unit ideal. -/
def numerators : Fin ((m + 1) * (n + 1)) → P := fun a =>
  (Fin.cons g f : Fin (m + 1) → P) (finProdFinEquiv.symm a).1 *
    (Fin.cons h k : Fin (n + 1) → P) (finProdFinEquiv.symm a).2

@[simp]
theorem numerators_pair (i : Fin (m + 1)) (j : Fin (n + 1)) :
    numerators K P m n g h f k (finProdFinEquiv (i, j)) =
      (Fin.cons g f : Fin (m + 1) → P) i * (Fin.cons h k : Fin (n + 1) → P) j := by
  simp [numerators]

variable [CompleteSpace K]

/-- The intersection algebra is an actual closed-ideal Tate quotient. -/
def algebra : PresentedStrictAffinoidAlgebra K :=
  RationalLocalization.algebra K P ((m + 1) * (n + 1))
    (g * h) (numerators K P m n g h f k)

/-- The constructed bounded structural map to the intersection algebra. -/
def baseMap : BoundedAlgHom K P (algebra K P m n g h f k) :=
  RationalLocalization.baseMap K P ((m + 1) * (n + 1))
    (g * h) (numerators K P m n g h f k)

/-- The actual quotient coordinate for a pair of extended numerator indices. -/
def fractionCoordinate (i : Fin (m + 1)) (j : Fin (n + 1)) :
    algebra K P m n g h f k :=
  RationalLocalization.fractionCoordinate _ _ _ _ _ (finProdFinEquiv (i, j))

end Langlands.Analytic.RationalIntersection
