# The actual vector point-to-Lie comparison under field extension

This is derived infrastructure for comparing actual root-field coordinates with
root coordinates over a splitting field. It uses the published natural vector
coordinates, their base change, and the actual dual-number Lie kernel. It is an
internal construction, with no independent claim from the literature.

For an affine group scheme with natural vector coordinates over a field `k`, a
field extension `K/k`, and any commutative `K`-algebra `A` in the same universe,
`vectorLieCoordinates_baseChange` identifies the epsilon coefficients before
and after the actual scheme-pullback comparison. The proof applies the existing
base-change formula for affine coordinates over the dual numbers of `A` and
takes each epsilon coefficient.

`vectorPointLieEquiv_baseChange` then identifies the point-to-tangent map in the
transported coordinates with the original point-to-tangent map. Applying the
injective Lie coordinate map reduces this to the existing affine-coordinate
base-change formula. The assertion covers all coefficient algebras, including
nonreduced ones. It does not yet identify independently chosen root coordinates
or prove a root-filtration comparison.

`vectorPointLieBaseChangeEquiv` transports the original equivalence through
the actual affine-point and tangent pullback equivalences.
`vectorPointLieBaseChangeEquiv_eq` proves that it equals the equivalence
constructed directly from the base-changed coordinates, by applying the
injective tangent comparison and the preceding theorem.
