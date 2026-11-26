# The real rectangle change of variables in the split tail

This module is the real counterpart of the Library's `ComplexGapRectangleShear`.

* `splitRectangle k q` separates a `k × (q + 1)` real rectangle into its first column and the
  remaining `k × q` rectangle (`splitRectangle_apply`), and `measurePreserving_splitRectangle` shows
  that it carries the rectangular measure built from an additive Haar measure `μ` on `ℝ` to the
  product of the row measure and the smaller rectangular measure.
* `firstRowCorrection k q x Z` is the `k × q` rectangle with entries `x i · Z 0 (j + 1)`: moving the
  factor with first column `x` to the left of the tail unipotent `Z ∈ N_{q+1}(ℝ)` produces it.
* `splitTailRectangle k q (Y, Z) = (first column x of Y, later columns of Y minus
  firstRowCorrection x Z, Z)` (`splitTailRectangle_apply`).

`RealGapRectangleShearStatement` (proved by `realGapRectangleShear`): for every additive Haar
measure `μ` on `ℝ`, `splitTailRectangle` carries the product of the rectangular measure on
`k × (q + 1)` rectangles and the entry Haar measure `entryHaar μ (q + 1)` to the product of the row
measure on `ℝ^k` with the product of the rectangular measure on `k × q` rectangles and the entry Haar
measure.

The proof splits the columns by reindexing the product of scalar measures; for fixed first column
and tail matrix the correction is a translation of the later rectangle, which preserves the additive
Haar measure (a skew-product argument). The empty later rectangle is included.
[Jacquet, *Archimedean Rankin–Selberg integrals*, Section 10.2, after (10.5)](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).
