# Rational-coordinate transport for compatible simple-root maps

Provenance: internal. This module specializes the published whole-root-map
compatibility interface to every rational coordinate, extending the existing
evaluation-at-one lemma. It uses the actual coefficient comparison and rational
Galois action of the Library and makes no new geometric existence claim.

For arbitrary fields `k,K : Type u` with an algebra structure, an affine group
scheme `G/k`, a split pinning of `G_K`, normalized simple-root maps `x`, and a
simple-root permutation representation `ρ`, the theorem
`SplitPinning.RootMapsGaloisCompatible.rationalPoints` proves
that the rational point with parameter `c` at root `a` transforms to the
point with parameter `σ c` at root `ρ σ a`. Its hypothesis is compatibility
of the entire coefficient curves, as defined in
`SteinbergFactorGaloisTransport`.

The proof first specializes coefficient-curve evaluation to the field `K`,
identifies the resulting affine-test point using root-map naturality and
`Lie.affineBaseChangeEquiv_constantPoint`, and then checks that evaluating
after coefficient conjugation agrees with conjugating after evaluation.
The latter equality is checked on polynomial coefficients and variables.
Applying whole-map compatibility and the injectivity of the actual
base-change coefficient comparison gives the asserted rational-point equality.

`PolynomialGalois.rootCoordinateConjugate` is the resulting transformation of
a root-indexed coordinate function: its value at `a` is
`σ (d ((ρ σ).symm a))`. The inverse permutation is needed because the coordinate
originally at a root moves to its image under `ρ σ`. Its identity law is proved
directly. This definition applies to any root index type in the same universe.

No assumption of Galoisness, finite degree, characteristic, perfectness,
infinitude or simple connectedness is used by these helper lemmas.
