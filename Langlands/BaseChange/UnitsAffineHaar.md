# Arbitrary Haar measure in affine unit coordinates

Let `R` be a second countable locally compact Hausdorff topological ring
whose units are openly embedded in `R`. For a compact open subgroup `U`
of the units, `UnitsAffineHaarStatement` says that `u ↦ u − 1` sends
multiplicative Haar restricted to `U` to a positive scalar multiple of
additive Haar restricted to the coordinate image.

The proof pulls back the multiplicative Haar measure to `U` and writes
it as its total mass times probability Haar. The Library's
`map_normalizedHaar_eq_restrict_of_units` gives the exact additive
normalization for the unit-value map. Translation by −1 preserves
additive Haar and translates the restriction along with its range.
The resulting scalar is finite and positive because the original
unit-value image is compact and open and the Haar mass of `U` is
finite and positive.

This is an internal corollary for arbitrary Haar measures in the
local Weyl change of variables.
