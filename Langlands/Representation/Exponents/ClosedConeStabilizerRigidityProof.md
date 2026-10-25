# Closed-cone stabilizer rigidity

`Langlands.Exponents.closedConeStabilizerRigidity` proves the exact
Library proposition
`Langlands.Exponents.ClosedConeStabilizerRigidityStatement`. For every
ordered block shape, real coordinate vector and strictly decreasing real
coarse-block parameter, the statement assumes blockwise zero sums, the
closed positive root cone for the selected permuted vector, and
stabilization of the shifted vector. It concludes that the same
permutation preserves each actual block and fixes the original vector.

The implementation lifts the coarse parameter to the actual coordinate
vector `a = t ∘ blockIndex B`. The published `blockIndex_monotone` and the
strict decrease of `t` make `a` antitone. Reindexing the sum through
`B.indexEquiv` and summing each actual block proves `∑ a_j v_j = 0`.

An auxiliary finite summation-by-parts argument proves that an antitone real
vector pairs nonnegatively with a vector in the closed positive root cone.
The argument uses Mathlib's `Finset.sum_range_by_parts`, extending the finite
vectors by zero only to express the range sums. The total-zero boundary term
vanishes and each remaining term has the sign dictated by antitonicity and
the proper partial-sum inequalities.

Apply this pairing to `v ∘ w`. The fixed shifted-vector equation identifies
`a - a ∘ w` with `v - v ∘ w`, so their pairing with `a` is nonpositive.
Reindexing the sum of squares by `w` gives
`∑ (a_j - a_(w j))² = 2 ∑ a_j (a_j - a_(w j))`.
The left side is nonnegative, hence zero. Each square vanishes, which proves
`a ∘ w = a`. Injectivity of the strictly decreasing coarse parameter proves
that `w` belongs to the actual block Weyl subgroup. The original fixed-vector
equation then gives `v ∘ w = v`.

This is internal finite real algebra, independent of representation theory.
The proof uses no occurrence, branch persistence, continuation, finite-length,
quotient-existence or classification theorem. Rank zero and one-block shapes
require no extra case assumptions.
