# Coefficients and weights in the model-star orbit computation

This internal helper keeps the original standard-character Whittaker coefficient
and representation fixed. For an upper-unipotent element `u`, a coefficient `W`
and `b = inverseTranspose(h) * w`, its two orbit formulas are

```text
W((h*u)^-1) = theta(u)^-1 * W(h^-1),
W(w * inverseTranspose((b*u)^-1)) = theta(u) * W(h^-1).
```

These identities follow from the published coefficient equivariance in
`Whittaker.GeneralLinear`, the group laws for inverse transpose and the Weyl
matrix, and the published character reversal of `reflectedUnipotent` in
`Whittaker.DualTransform`. In the second identity the unipotent element acting
on `h^-1` is `reflectedUnipotent(u^-1)`, whose standard character is `theta(u)`.
Neither identity assumes smoothness, irreducibility, or a nonzero functional.
They include `r = 0`.

The scalar factor `adjacentRankOrbitWeight abv chi h s` is
`chi(det h) * |det h|^s`. The exponent is an arbitrary complex number; the inner
model uses `s = r/2`. Right-unipotent multiplication preserves the determinant,
the determinant weight and their scalar product. The reflected base satisfies
`det b = det w * (det h)^-1` and `|det b| = |det h|^-1`.
The absolute determinant of `w` is one because `w*w = 1` and an absolute value
is nonnegative. Positivity of the absolute determinant makes the usual complex
power of its inverse equal the power with negated exponent. Thus

```text
OrbitWeight(abv, chi^-1, b, s)
  = chi^-1(det w) * OrbitWeight(abv, chi, h, -s).
```

The final regularity lemma works on every canonical p-adic field, for an original
complex module in an independent universe with no topology or norm supplied.
For every smooth representation, actual coefficient-image vector, rectangular
Schwartz function, continuous quasicharacter and complex exponent, the function
`Phi(K(h))*W(h^-1)*chi(det h)*|det h|^s` is continuous with compact support.
Continuity uses the continuous kernel, smooth-coefficient continuity and the
published continuous determinant weight. Compact support is the published
`adjacentRankPure_hasCompactSupport`, followed by multiplication by the two
scalar weights.

All results are internal consequences of the named published constructions and
support theorem. They provide orbit and regularity adapters for the fixed-action
adjacent-rank model-star proof and do not assert its Fourier or integral identity.
