# L2 assembly from a finite Cartan lattice cover

Author: Worker 19.

`CartanLatticeL2Statement` is an internal analytic assembly statement for any
topological group, any algebraic complex representation, and an independently
sized finite coordinate type. It assumes admissibility and a specified genuine
unitary central character. The measure is any supplied Borel Haar measure on
the quotient by the full group center.

The cover premise expresses every group element as
`k₁ * τ n * t * k₂ * z`, with both compact-side factors in a specified subgroup
`K`, the middle factor in a finite set `T`, and `z` in the full center.
No algebraic, homomorphism, compactness, or openness property of `τ` or `K`
is needed once the displayed cover and bounds are available.

For a fixed nonnegative coordinate weight `w`, the first estimate bounds the
measure of the image of each double coset `K * (τ n * t) * K` by
`ofReal (D * ∏ i, w i ^ n i)`, using one nonnegative constant `D`.
The second estimate bounds every smooth coefficient uniformly on these cells
by `C * ∏ i, a i ^ n i`, where `C` and the nonnegative coordinate radii `a`
may depend on the vector and smooth functional. Each radius satisfies
`a i ^ 2 * w i < 1`. No relation between different coordinates' weights is
assumed.

The conclusion is the Library's actual `IsSquareIntegrableModCenter`.
The intended derivation takes the finite union over `t` for each `n`,
uses subadditivity to multiply the volume constant by the cardinality of `T`,
and applies `finiteLatticeCellL2` with polynomial degree zero. The descended
coefficient norm is measurable by `aestronglyMeasurable_coefficientNorm`.
The cover descends because the last factor is central.

This packaging is derived from these published analytic mechanisms rather
than attributed to a separate literature theorem. It retains empty finite
coordinate types and empty translating sets. It does not assert the cover,
either estimate, or any geometric or spectral existence result. Those
premises must be discharged by actual proofs when this statement is applied
to the general rational strict Jacquet criterion.
