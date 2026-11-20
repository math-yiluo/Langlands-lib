# Compact-open double cosets and orbital integrals

This module derives the compact-open indicator formula from the Library's
actual left quotient, its compatible measure, and its twisted orbital integral.
The argument is an internal consequence of the compact-open orbit restriction
formula and countable additivity.

`compactOpenDoubleCoset` sends a double coset to its image in the left quotient.
The subset attached to a representative `g` is the image of `gK`. These sets
are open and pairwise disjoint. For a separable ambient group they are indexed
by a countable type. Evaluating the published compact-open restriction identity
on the whole quotient gives their masses as `μG(K) / μH(H ∩ gKg⁻¹)`.

For an endomorphism taking `K` into `K`, membership of `g⁻¹ δ θ(g)` in `K`
is invariant on each double coset of the twisted centralizer and `K`.
The descended integrand is the complex indicator of the union of the qualifying
quotient subsets. Its integral is the `toReal` of the sum of their extended
nonnegative masses, coerced to `ℂ`. This uses the same total Bochner integral
as the Library's definition, including its value in the infinite-mass case.
