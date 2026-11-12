import Mathlib.Data.Nat.Basic

/-! # Distance from the middle pair of an even path -/

namespace Langlands.GroupScheme.SplitPinning

/-- The distance of the path position `i` from the middle pair `{m - 1, m}` of a path with
`2 m` vertices: `m - 1 - i` on the left half and `i - m` on the right half. Both middle
positions have distance `0`. -/
def middleDistance (m i : ℕ) : ℕ := if i + 1 < m then m - 1 - i else i - m

end Langlands.GroupScheme.SplitPinning
