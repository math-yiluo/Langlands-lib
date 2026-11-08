# Scalar axioms for actual torus restriction followed by field restriction

This is an internal consequence of the canonical torus restriction and actual
field restriction, on the unchanged family
`torusFieldRestrictedRootFunctionFamily`. Work over arbitrary fields `K/k` in
universe `u`, with a smooth affine actual group `G/k`, a split torus `S/k`,
and an actual split torus `T/K` monomorphically included by `j:T→G_K`.
Retain the upper opposite-factor-pair hypothesis, an upper root-datum
valuation, and an actual map `f:S_K→T` with `groupHom f ≫ j = i_K`.

The normalization theorem transports both upper torus support laws along the
factorization equality, then applies actual field normalization. The exact
identity criterion applies the torus identity criterion to extended points,
then uses injectivity of affine rational scalar extension. That injectivity
is proved by the actual coefficient-point comparison and injectivity of
extension of coordinate algebra maps.

All finite original root levels were identified with exact subgroup
preimages in `RootValueTorusFieldRestriction`; their identity, multiplication
and inversion laws give V1 here. V4 is the proved canonical torus doubling
identity applied to the pulled-back original character and original doubled
root-group point. Character pullback commutes with doubling, and the
factorization equality identifies the actual inclusion throughout.

V0 requires compatibility of the upper valuation with an additive real unit
character which is nontrivial on the image of **original** field units.
Inherited covariance and the exact identity criterion construct
`torusFieldRestrictedRootValueEmbedding`, an injection from the integers into
the actual original root-value image, by
`IsSplitTorusCompatible.rootValueEmbedding`. Its implemented proof uses an actual
nonidentity rational root point and integral powers of a torus point. This
gives infinitely many values on each original actual root group. The
cardinal bound follows from this infinite image. Nontriviality only on upper
field units is not sufficient for this argument.

No full valuation on the lower torus over `K` is assumed. These scalar laws
do not establish initial or adapted existence, reflection V2, opposite V5,
building geometry or the supplied integral-model comparison.
