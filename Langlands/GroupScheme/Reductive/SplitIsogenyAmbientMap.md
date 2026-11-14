# Recovering an ambient homomorphism from a local-isogeny graph

This internal construction turns established geometry of an actual
`LocalIsogenyGraphEnvelope` into an ambient homomorphism. It works over every
field, with potentially different source and target tori and any indexing
universe for the local family. Invertibility of the first projection is an
explicit hypothesis throughout; the module does not prove it.

In the namespace
`Langlands.GroupScheme.RootDatumIsogenyRealization.LocalIsogenyGraphEnvelope`,
`realizationHom` is the composite of the inverse first graph projection with
the second projection. `first_realizationHom` proves its projection identity.
The graph's distinguished torus lift and local lifts then give
`torus_realizationHom` and `local_realizationHom`: the ambient map restricts to
the original actual torus map and to every supplied local isogeny. Cancellation
of the first projection proves `realizationHom_unique`.

`realizationHom_isIsogeny` additionally assumes that the second projection is
an isogeny. The inverse first projection is an isomorphism, hence an isogeny,
and composition preserves finite, flat and surjective scheme morphisms. The
conclusion uses the full scheme-theoretic meaning of an isogeny, without any
smoothness or reducedness assumption on its kernel.

`exists_realization_of_graph_projections` specializes these constructions to
the actual torus map `torusMap hT' f` of a finite reduced root-datum isogeny.
The source and target tori are split, all four actual lattices are finitely
generated, and the two root-datum pairings equal the respective actual torus
pairings. The natural-number exponent is arbitrary. The conclusion supplies
an actual ambient isogeny, an actual torus isogeny, their commuting square,
and the exact prescribed character and cocharacter equations. The character
equation is `torusMap_comp`; the transpose equation is `comp_torusMap`; and
`torusMap_isIsogeny` supplies finite-flat-surjective torus geometry. The two
ambient projection hypotheses are retained and are not proved by this result.

The provenance is a derived categorical construction from the graph-lift
identities, the actual torus-map construction, and the published stability
of isogenies under composition. No new literature assertion is encoded.
The companion `SplitIsogenyReduction` module supplies the conditional
fixed-torus extension deduction from realization and the induced-map
assertion; neither companion proves these remaining geometric inputs.
