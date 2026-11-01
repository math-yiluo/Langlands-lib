# Geometric summability on the opposing-twist cone

This internal analytic package continues the elementary cone estimates in
`TwoBlockLowerFixedSliceSupport`. It derives a summable lattice majorant; it
does not yet assert convergence of the lower-quotient integrand.

`geometricWeight r lam` is `r` to the sum of the absolute integer diagonal
exponents. For `0 ≤ r < 1` its sum over the entire finite integer lattice is
finite. The proof splits an integer series into its nonnegative and
nonpositive parts, both geometric series, then takes finite products of
nonnegative summable coordinate functions. The product argument follows the
empty-type/option induction also used by the published
`Langlands.summable_fintype_nat_prod`, with an arbitrary coordinate type in
place of the natural numbers. Empty lattices are included.

On `OppositeCone M s lam`, the previously proved inequality bounds the
absolute-exponent sum by `twistDegree s lam + n * (2 * M)`. For `q > 1`,
`B ≥ 0` and `u ≥ 0`, monotonicity of real powers converts
`B ^ torusSize lam * q ^ (-u * twistDegree s lam)` to at most
`q ^ (u * n * (2 * M)) * geometricWeight (B * q ^ (-u)) lam`.
The prefactor may depend on the cone and the real twist.

There is one nonnegative real threshold depending only on `q > 1` and
any real `B`, after which `u ≥ 0` and `B * q ^ (-u) < 1`.
Choose a natural number `N` with `B < q ^ N`; any real `u > N` works.
When additionally `B ≥ 0`, the ratio satisfies `0 ≤ B * q ^ (-u) < 1`.
Consequently the expression supported on any such cone is summable, with
the same threshold for every cone bound and coordinate subset.
These are derived geometric-series and elementary real-power consequences;
no representation-theoretic or quotient integrability premise is used.
