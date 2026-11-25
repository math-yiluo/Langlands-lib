# Algebraic spaces from étale-local scheme representations

This is an internal construction from the published
`LocalRepresentation.chartProductIso`, open-cover gluing, kernel-pair diagonal
descent, and effective fppf descent of separated locally quasi-finite schemes.
It cites no additional literature theorem.

A supplied scheme representation of an fppf sheaf after restriction along
`j : U → B` gives a chart on the full category of schemes over `B`.
`chartProductIso` identifies its source with the product of the sheaf and
the functor represented by `U`. Base change stability therefore proves that
this chart is representable étale if `j` is étale and representable surjective
if `j` is surjective.

For a single étale surjective `j`, the chart has a represented kernel pair
with étale projections. It is locally surjective for the fppf topology.
`KernelPair.hasRepresentableDiagonal_of_isPullback`, using the published
`fppfSeparatedLocallyQuasiFiniteDescent` proof, gives the representable diagonal.
Together these data make the original fppf sheaf an algebraic space; diagonal
representability is derived, not assumed.

For any same-universe étale covering family, first restrict the sheaf to the
scheme coproduct of the base members. This restriction remains an fppf sheaf
by continuity of `Over.map`. The supplied representations cover that coproduct
by its open components, so the published open-cover gluing constructs a scheme
representation there. The coproduct maps étale surjectively to the original
base, and the preceding single-map result applies. The indexing type need not
be finite or nonempty, and no quasi-compactness or separation hypothesis is
added to the cover.

All representation inputs are actual natural isomorphisms on every relative
scheme test, in the same universe. `LocalRepresentation.ofCover` equips the
original sheaf with the resulting algebraic-space structure, preserving its
underlying presheaf definitionally. The conclusion is algebraic-space
representability only; effective descent to a scheme requires further geometry.
