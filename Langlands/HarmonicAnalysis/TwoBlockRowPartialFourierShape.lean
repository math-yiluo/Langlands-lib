import Langlands.HarmonicAnalysis.TwoBlockRowPartialFourierData
import Langlands.Representation.RankinSelberg.TwoBlockJacquetData

/-!
# The positive two-block placement of a row

For block ranks `m 0 + 1` and `m 1 + 1` with `(m 0 + 1) + (m 1 + 1) = t + 1`, the contiguous
placement `contiguousEquiv (TwoBlockJacquet.blockRanks_add h)` sends the coordinates of the two
blocks to the block inclusions `(succBlockShape m h).index 0` and
`(succBlockShape m h).index 1` used for the two-block data of JPSS 1983, Sections 4.6-4.7.
This adapter keeps representation theory out of the generic row module.
-/

namespace Langlands.HarmonicAnalysis.TwoBlockRowPartialFourier

open Langlands.RankinSelberg

universe uR

variable {R : Type uR} {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

/-- The contiguous placement of the two blocks of `succBlockShape m h` in a row of length
`t + 1`. -/
def succBlockEquiv : Fin (m 0 + 1) ⊕ Fin (m 1 + 1) ≃ Fin (t + 1) :=
  contiguousEquiv (TwoBlockJacquet.blockRanks_add h)

theorem succBlockEquiv_eq :
    succBlockEquiv h = contiguousEquiv (TwoBlockJacquet.blockRanks_add h) := rfl

/-- The first block is placed by the first block inclusion of `succBlockShape m h`. -/
@[simp] theorem succBlockEquiv_inl (i : Fin (m 0 + 1)) :
    succBlockEquiv h (Sum.inl i) = (succBlockShape m h).index 0 i := by
  rw [TwoBlockJacquet.index_zero]
  rfl

/-- The second block is placed by the second block inclusion of `succBlockShape m h`. -/
@[simp] theorem succBlockEquiv_inr (j : Fin (m 1 + 1)) :
    succBlockEquiv h (Sum.inr j) = (succBlockShape m h).index 1 j := by
  rw [TwoBlockJacquet.index_one]
  rfl

theorem first_succBlockEquiv (z : Fin (t + 1) → R) (i : Fin (m 0 + 1)) :
    first (succBlockEquiv h) z i = z ((succBlockShape m h).index 0 i) := by
  rw [first_apply, succBlockEquiv_inl]

theorem second_succBlockEquiv (z : Fin (t + 1) → R) (j : Fin (m 1 + 1)) :
    second (succBlockEquiv h) z j = z ((succBlockShape m h).index 1 j) := by
  rw [second_apply, succBlockEquiv_inr]

@[simp] theorem join_succBlockEquiv_index_zero (w : Fin (m 0 + 1) → R) (v : Fin (m 1 + 1) → R)
    (i : Fin (m 0 + 1)) :
    join (succBlockEquiv h) w v ((succBlockShape m h).index 0 i) = w i := by
  rw [← succBlockEquiv_inl, join_inl]

@[simp] theorem join_succBlockEquiv_index_one (w : Fin (m 0 + 1) → R) (v : Fin (m 1 + 1) → R)
    (j : Fin (m 1 + 1)) :
    join (succBlockEquiv h) w v ((succBlockShape m h).index 1 j) = v j := by
  rw [← succBlockEquiv_inr, join_inr]

end Langlands.HarmonicAnalysis.TwoBlockRowPartialFourier
