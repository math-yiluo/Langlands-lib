# Determinant-one corner parameters

This internal prerequisite separates the determinant of the integral Iwasawa
parameter from the corner parameter. It does not prove compact Haar-average
realization or the matrix functional-equation comparison.

For a tail of units `t` and an arbitrary invertible matrix `k`, the existing
`diagPoint F (1, (t,k))` has determinant `det k`. The construction
`specialLinearCorner F (t,k)` multiplies it on the left by the inverse of
`diag(det k,1,…,1)`. Its determinant is exactly one for every parameter, without
an integrality assumption.

The scalar coordinate `glOneDeterminantLift k` is the one by one matrix with
entry `det k`. The pointwise factorization is

```text
diagPoint F (g,(t,k))
  = rankOneDiagonal n (g * glOneDeterminantLift k)
      * specialLinearCorner F (t,k).
```

The proof uses the multiplicativity of diagonal matrices and cancellation.
For integral `k`, the correction has determinant of normalized absolute value
one, so its inverse-modulus density in `glOneMeasure F n` is one.
The proof of `measurePreserving_glOneDeterminantLift` applies the published
multiplicative-density translation formula to the homomorphism
`g ↦ weight F n (g,1)`. The density of the correcting element and its inverse
is one. Thus multiplication by this element preserves the actual weighted
scalar measure, with no additional constant.

The two scalar transport theorems apply this measure-preserving translation
and its measurable embedding to an arbitrary complex-valued function on the
matrix group. They give equality of the totalized integrals and equivalence
of actual Bochner integrability. They do not assert joint convergence in all
Iwasawa parameters or realization of an averaging measure.

The definitions and identities are derived from the published Iwasawa
coordinates and `determinantRankOne`. They address the determinant-one
coordinate used in JPS 1979, Section 4.3, but no source theorem is asserted here.
