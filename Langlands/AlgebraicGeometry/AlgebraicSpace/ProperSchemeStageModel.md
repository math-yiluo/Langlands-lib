# Actual proper scheme models at an affine limit stage

This internally derived unit packages a proper locally finitely presented
scheme model at an actual original stage of a cofiltered affine diagram,
with its actual cartesian comparison square. `sourceIso` expresses this
square as an isomorphism of schemes over the limit; `spaceIso` combines
Yoneda with the scheme-base-change comparison to give a whole-space
isomorphism with the base-changed stage scheme.

`exists_properSchemeStageModel` applies the published
`SchemeLimitModel.schemeFilteredProperModelExistence` theorem to the global
sections colimit of the actual affine limit diagram. The affine spectrum
isomorphisms transfer its model and cartesian square back to the original
scheme stage. Properness and local finite presentation are preserved by these
isomorphisms. The scheme source is arbitrary, with local finite presentation,
quasi-compactness and quasi-separatedness over the limit, and an explicit
properness hypothesis.

The provenance is internal: the published proper scheme model-existence
proof, the affine-limit/global-sections colimit equivalence, affine spectrum
naturality and the existing whole-space scheme base-change comparison. It
does not assert a proper scheme cover of any algebraic space or eventual
properness of a space; those remain separate consumer obligations.
