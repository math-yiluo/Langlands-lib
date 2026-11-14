# Actual doubled-root jumps from supplied quadratic unitary coordinates

This internal helper connects the literal central subgroup of supplied
`RootUnitaryCoordinates` with ordinary affine roots in the doubled direction.
It is derived from the published coordinate interface and the V4 axiom of
an actual apartment valuation, using the generic coordinate transport in
`CoordinateAffineRootJumps`.

`RootUnitaryCoordinates.centralEquivDouble` restricts the supplied unitary
coordinate map to an isomorphism from its zero-first-coordinate subgroup
onto the actual rational root group `U_{2a}(k)`. Its membership follows from
the supplied `double` identification; injectivity follows from the original
coordinate isomorphism, and the other direction of `double` gives
surjectivity. The implementation composes the standard subgroup-image
equivalence for an injective homomorphism with equality of the image
subgroup, using a private generic helper before specializing to the actual
root groups. It sends a central parameter to the same ambient rational
point as the original map.

Suppose `a` and `2a` are relative roots, `w` is an additive valuation of
the coordinate extension field, `x` is an actual apartment point, and
`x.val a (e p) = depthA w p` holds for every coordinate. Then V4 forces
`x.val (2a) (e z) = depthDouble w z` on the literal central subgroup.
The proof uses V4 and checks the equality between twice a half-depth and
the full depth for both finite values and infinity. No second depth
comparison is required.

If the prescribed torus is split and `4a` is not a relative root, an affine
functional with derivative `rootForm i (2a)` is an ordinary affine root
exactly when its value at `x` is a central depth jump: the closed ball in
the literal central subgroup is not contained in its strict ball. Here the
double-root subgroup of `2a` is trivial. The proof applies the generic
coordinate bridge with `centralEquivDouble`, the depth equality just
derived, and the trivial quotient subgroup, then removes multiplication
by that subgroup.

No coordinate-existence theorem, actual depth comparison in the `a`
direction, central jump-value computation, or unconditional quasi-split
indivisible-lift theorem is claimed. There are no field-characteristic,
residue-characteristic, residue-perfection, or conjugation-invariance
assumptions on this conditional bridge.
