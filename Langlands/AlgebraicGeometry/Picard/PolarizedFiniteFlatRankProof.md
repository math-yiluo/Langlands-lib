# Native rank of a polarized finite-flat endomorphism

`polarizedFiniteFlatRank` proves the complete unchanged
`PolarizedFiniteFlatRankStatement` in arbitrary universe `u`. An actual finite
flat endomorphism of the specified smooth proper geometrically connected
scheme has native rank `q ^ g` at every target point when it pulls an actual
ample line bundle back to its `q`-th tensor power, with `q > 0`.

This is an internal assembly of published actual geometric and cohomological
comparisons. Its source specialization is documented in the paired statement;
the implementation uses Euler polynomials directly. No polynomiality,
positivity, degree formula, supplied rank, or cancellation certificate remains
as an outer hypothesis.

For the ample bundle `L`, `smoothProperLineBundleEulerPolynomial` supplies
finite cohomology of every nonnegative tensor power and a rational polynomial
`P` evaluating to their actual integer Euler characteristics. Ampleness makes
its degree exactly `g` and its leading coefficient positive, hence nonzero.
Applying the same theorem to the actual pulled-back line bundle supplies a
polynomial `Q` for its tensor powers; ampleness of that pullback is not needed
for this polynomial's existence.

`finiteFlatPullbackEulerLeadingCoefficient` gives

```text
Q.leadingCoeff = (f.left.finrank x : rational) * P.leadingCoeff.
```

The native rank in this equality comes from the actual finite algebra and its
generic free chart, transported through coherent Euler comparison, affine
pushforward, and the projection formula as described in that proof's Markdown.
Thus the equality calculates the native scheme rank of the given map.

Extract the actual polarization isomorphism from its `Nonempty` witness.
`polarizedTensorPowerEulerDilation` powers it, uses pullback compatibility with
actual tensor powers, and flattens the exponents to obtain actual sheaf
isomorphisms between the `n`-th power of `f* L` and the `q * n`-th power of
`L`. Isomorphism invariance of actual finite cohomology and Euler
characteristic then gives

```text
Q(n) = P(q * n)
```

for every natural `n`, including zero. The rational-polynomial theorem
`scalar_eq_pow_of_eventually_nat_eval_dilation` identifies `Q` with the
composition of `P` and multiplication by `q`, compares leading coefficients,
and cancels the nonzero coefficient of `P`. It obtains
`(f.left.finrank x : rational) = (q : rational) ^ g`; injectivity of the natural
cast gives the asserted equality of natural numbers. The target point `x`
was arbitrary. The proof preserves arbitrary characteristic, `q = 1`, and
`g = 0`.
