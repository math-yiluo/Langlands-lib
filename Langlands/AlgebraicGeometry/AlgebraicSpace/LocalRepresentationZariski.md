# Gluing local scheme representations of a Zariski sheaf

This internal variant of `SliceOpenGluing` and `LocalRepresentationGluing`
uses only the big Zariski sheaf condition on the actual slice over a scheme.
It retains the existing actual scheme gluing, with no fppf sheaf condition on
the input presheaf. The presheaf has values in `Type (u + 1)`; its local
representations are isomorphisms on the full slice over each open base
chart, for an arbitrary open cover indexed in universe `u`.

In `SliceOpenGluing.Zariski`, the imported `sliceData`, `schemeData`,
`structureMap`, `glued` and `toGlued` are used without changing their
scheme objects or morphisms. `oneHypercover` verifies directly that the
same chart and overlap families cover in the big Zariski slice topology.
The chart covers are therefore sufficient to glue sections of a Zariski
sheaf using the hypercover multifork limit.

`yonedaGluedToSheaf` is the actual comparison from the represented sheaf
of the glued scheme to the input sheaf. Its restrictions along the open
chart inclusions equal the supplied chart transformations. If those charts
are locally surjective for the Zariski topology, so is this comparison.
It is also locally injective: pull back the open chart cover along each
of two morphisms into the glued scheme; on their common refinements,
equality of sheaf values identifies their maps through the represented
overlaps, and thus their maps into the gluing. The sheaf local-bijectivity
criterion makes the comparison an isomorphism.

`baseCoverSieve_mem_zariski` puts an arbitrary open cover of the base
in the covering sieves of its terminal slice object. The proof of
`charts_locallySurjective_zariski` pulls back this sieve to each test
scheme. The existing all-test `chartProductIso` ensures that a section
and a lift to an open base chart together supply a lift to its local
representing scheme.

Finally, `LocalRepresentation.exists_representation_zariski` applies the
preceding open-chart gluing to a Zariski sheaf and supplied local full-slice
representations. Its conclusion is an actual scheme over the original base
and a natural isomorphism of its lifted Yoneda presheaf with the original
presheaf. No finite, affine, separated, or quasi-compact hypothesis occurs.

This is an internal adaptation of the already published Library gluing
proof: the geometry and lifted-Yoneda comparison are reused, while every
covering and section-gluing argument is made directly in the Zariski
topology. Existing copyright and attribution notices from the reused Lean
source are retained. It does not prove effective scheme descent for an
etale cover and makes no new literature translation claim.
