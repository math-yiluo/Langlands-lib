# L2 integration from polynomial-geometric finite lattice cell bounds

`Langlands.finiteLatticeCellL2` proves the complete
`Langlands.FiniteLatticeCellL2Statement`, with independent ambient-space and
finite-coordinate universes. Its ingredients are the published
`finiteNatLatticeENNRealSummability` and `countableCellLpUpper`.

Write `H(n) = 1 + ∑ i, n i`. The coefficient majorant is nonnegative.
Squaring it and multiplying by the volume majorant gives

`(C² * D) * H(n)^(2*d) * ∏ i, ((a i)² * w i)^(n i)`.

The proof verifies this equality using finite-product and natural-power
identities. All residual weights are nonnegative and strictly below one.
The finite natural-lattice summability theorem therefore makes the ENNReal
sum of these bounds finite, with polynomial degree `2*d`. Natural powers
agree with the real powers in that theorem on the nonnegative height.

Applying `ENNReal.ofReal` to the pointwise coefficient bounds gives upper bounds
for the extended norms. Multiplication by the cell measures is bounded term by
term by the finite residual series. The countable-cover theorem then yields
`MemLp f 2 μ`. The coordinate tuple type is countable, and the cover need not
be measurable or disjoint. No division by a weight occurs, so zero weights
and the empty coordinate type are included.

This is an internal analytic composition. It does not construct cells or prove
the coefficient or volume hypotheses for any representation or group.
