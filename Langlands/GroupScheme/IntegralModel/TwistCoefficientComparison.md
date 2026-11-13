# Coefficient pullback and semilinear twisting

This internal construction compares coefficient pullback with actual
coefficient twisting. All rings and schemes have arbitrary common universe
`u`. The input consists of domains R and A with specified fraction fields K
and L, the coefficient algebras and their two scalar towers, an actual
integral model N over R, and compatible endomorphisms of the four spectra.
No base map is assumed invertible.

`baseChangeSquareIso` expresses the model coefficient generic comparison as
the public commuting-square comparison followed by the pullback of the
original chosen generic identification. The theorem
`baseChangeGenericIso_eq_square` proves that this is exactly the published
`baseChangeGenericIso`, including its prescribed identification. Its proof
cancels the pulled-back original generic isomorphism and compares projections
to the original model using the published projection formula.

The auxiliary `squareComparison_inv_fst_fst` records the inverse square
comparison's projection formula. The general `squareComparison_cube` states
that the two paths through a commuting coefficient cube agree. To prove it,
the code collapses the target pullback tower, compares projections to the
original group, and uses the projection formulas for actual square and tower
comparisons.

`twistBaseChangeIso` is an actual compatible integral-model isomorphism from
the twist of `N.baseChange A L` to `(N.twist ...).baseChange A L`. Its integral
isomorphism is the commuting-square comparison for the integral coefficient
maps. Its specified generic isomorphism is the commuting-square comparison
for the field coefficient maps. The four endomorphisms are required to
commute with their respective fraction-field inclusions, and the integral
and field endomorphisms must each commute with the corresponding coefficient
extension. The proof of its exact generic compatibility uses the public
coefficient comparison identity, the commuting cube identity, and naturality
in N's original generic identification.

This is an internal consequence of the published actual pullback and model
base-change constructions. It supplies a comparison needed before descending
an upstairs semilinear isomorphism between supplied finite coefficient
models. It constructs no such upstairs extension, finite field of definition,
Galois automorphism lift, arithmetic cover or final descended model, and does
not prove KP Fact 2.10.16.
