# Normalized spherical torus recursion

Author: Worker 1767.

This internal helper constructs the half-modulus weighted evaluation of the
dominant Jacobi–Trudi polynomial. Pair counting identifies the exponent of the
half modulus: the radical multiplicity and half modulus together give the
positive standard Hecke normalization. All residue cardinalities in these
identities are assumed positive.

The implementation first rewrites the sum of positive-root differences as
`sum_i (n - 2 i) α_i` in rank `n + 1`, using the cardinalities of the indices
above and below each index. For a subset, differences of its indicator count
the two orientations of separated pairs. Their sum is `k (n + 1 - k)`.
Since the square of the positive real square root of `q` is `q`, this proves
the exact complex identity between `q` to the radical count times the
subset half modulus and `sqrt q ^ (k (n + 1 - k))`.

The elementary symmetric polynomial evaluates to the published unramified
`elementaryCoefficient` of the parameter tuple. Evaluating the
dominance-restricted Pieri identity and multiplying by the half modulus gives
the exact minuscule recursion, with one term for each subset of size `k` and
the weight `q` to its radical count. The coefficient is one at zero, vanishes
off antitone weights, and agrees with `halfModulus q α * satakeSchur x α`
on every nonnegative antitone integral weight.

The construction is algebraic, with no Whittaker model hypotheses or analytic
convergence claim. The proof derives its identities from interval and
separated-pair counting, square roots and integer powers, and the previously
proved polynomial Pieri identity.
