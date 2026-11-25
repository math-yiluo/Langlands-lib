# Finite vector-bundle series on isomorphic representatives

This internal derived module transports the Library's unchanged
`HasVectorBundleSeries` and `HasFiniteVectorBundleSeries` predicates through
an isomorphism of group schemes over any base scheme, at arbitrary universe
`u`. No affineness or field hypothesis on the base is required.

`HasVectorBundleSeries.of_iso e h` preserves the supplied length. At length
zero, a point becomes the identity after composition with the inverse
isomorphism, so injectivity of the induced point equivalence proves the
exact all-test triviality clause. At positive length, retain the first
kernel group `K`, quotient group `V`, and series on `K`; compose its
inclusion with `e.hom` and precompose its quotient map with `e.inv`.
Closedness is preserved by the underlying scheme isomorphism. The
published range-composition formula transports normality, and
`RelativeRoot.IsFppfQuotient.comapIso` transports the actual flat,
surjective, locally finitely presented quotient and its all-test kernel.
The quotient group and its actual vector-bundle data are unchanged.

`HasFiniteVectorBundleSeries.of_iso` applies this construction at the
supplied existential length. The selected data definition
`seriesWitnessOfIso` sends a subtype-valued length-and-proof witness to the
corresponding witness for the isomorphic group. Its value projection is
the original length by definition, as recorded by `seriesWitnessOfIso_val`.

`hasFiniteVectorBundleSeries_of_representatives` uses the published
comparison isomorphism between two representations of one all-test
subgroup functor, then transports the finite series. It assumes a series
on one representative and does not construct a filtration or assert
representability.

The proof is derived from the recursive series definition, the Library's
all-test point equivalence and represented-subgroup comparison, and the
range and fppf-quotient transport in `Rational.SplitUnipotentTransport`.
It adapts that module's split-series transport to actual vector-bundle
quotients, retaining the stronger linear sheaf data required by
`RelativeUnipotent.Basic`.
