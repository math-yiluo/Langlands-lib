# The multiplicative quotient step of Borel normalizer induction

Authors: Worker 1369; Worker 1446 supplied the reused dimension and local
normalizer induction helpers.

This internal consequence uses the existing all-test subgroup and fppf
quotient definitions. The field has arbitrary characteristic and universe
`u`. The final normalizer assertions assume that the field is algebraically
closed.

`RelativeRoot.IsFppfQuotient.inclusion_comp_eq_one` works over any scheme.
If `q : G → Q` is an fppf quotient with actual kernel range equal to the
range of `z : Z → G`, then the composite of the underlying morphisms
`z` and `q` is the constant identity morphism. The proof tests the range
equality on `Z` itself and applies the existing scheme-kernel membership
criterion.

`RelativeRoot.IsFppfQuotient.gm_induction_properties` starts with a smooth
connected affine group `G`, an affine group `Q`, a closed embedding
`z : Gm → G` and a supplied fppf quotient `q` with kernel range equal to
`range z`. It proves that the projection `q` is smooth, that `Q` is smooth
and connected, and that `Lie.dimension Q < Lie.dimension G`. These
properties are conclusions of this helper.

The source is quasi-compact because it is affine over a field, which
implies quasi-compactness of `q`. The existing represented-kernel
smoothness theorem applies to the smooth kernel `Gm`, so `q` is smooth.
The smooth surjective source descent theorem then makes `Q` smooth
because the composite with its structure morphism is the smooth
structure morphism of `G`. Surjectivity transfers connectedness. Finally,
the closed embedding is monic and the preceding kernel equation shows
that `q` kills it. Worker 1446's
`Lie.dimension_lt_of_smooth_kills_gm` gives the strict decrease of the
finite rank of the actual additive dual-number identity kernel. No
comparison with a separate geometric dimension is used.

`normalizer_borelRange_eq_of_fppf_gm_quotient` additionally takes the exact
smaller-dimension normalizer induction hypothesis, a subgroup morphism
`i : B → G`, a Borel morphism `iQ : BQ → Q`, and the equality
`(range iQ).comap q = range i` on every test scheme. It applies the
induction hypothesis to the smooth connected affine group `Q` using the
strict decrease just proved. The published construction in
`Absolute.QuotientNormalizer` transfers its rational normalizer equality
to `G`. That transfer uses lifting only of algebraically closed ground
field points through the locally finite type surjective morphism `q`.

`borelPointOfFppfGmQuotient` chooses an actual ground field point of `B`
lifting any point of `G` that normalizes `range i` on ground field points.
Its companion theorem identifies the composite with `i` with that
original point. Choice is applied to the range membership obtained from
the preceding normalizer equality.

The provenance is this composition of existing actual-kernel, smooth
descent, Lie-dimension and rational-normalizer results. A centrality
assumption is unnecessary once a quotient with the specified kernel
exists. The intended central quotient consumer must still construct
that affine fppf quotient and its Borel with the exact all-test inverse
image. This module does not prove existence of those data, the
unconditional Borel normalizer theorem, or a parabolic normalizer
theorem.
