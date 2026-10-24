# Proof of the root-coordinate spectral weight

`Langlands.RankinSelberg.rootSpectralWeight` proves the named
`RootSpectralWeightStatement` for every field, supplied topological data and
natural rank parameter in that proposition.

For the integral subgroup, the proof uses
`Conductor.valuation_det_of_mem_integralSubgroup` to obtain valuation one for
the determinant. This also proves the determinant is nonzero. Applying the
value-group isomorphism gives discrete valuation one and therefore order zero.
The formula for `T.normalizedAbs` then gives determinant norm one.

For the spectral formulas, the proof extracts the determinant identity from
`rootCoordinateChange`, applies the normalized absolute value to the finite
product, and uses multiplicativity of the determinant and the given
determinant-norm-one condition on the right factor `k`.

A private finite-product lemma distributes complex powers over nonnegative
real factors, by induction and Mathlib's `mul_cpow_ofReal_nonneg`. A second
private lemma combines a natural power followed by a complex power. Its
argument conditions hold because a nonnegative real number has complex
argument zero. These two identities turn the determinant power into the
product with complex exponents `(i + 1) * s`.

Finally, the proof takes norms of the finite product. Each unit coordinate
has strictly positive normalized absolute value; Mathlib's
`norm_cpow_eq_rpow_re_of_pos` therefore gives precisely the real power with
exponent `(i + 1) * s.re`.

This is an internal algebraic and complex-power adapter. It assumes no
representation-theoretic or analytic conclusions and includes rank one and
every complex spectral parameter.
