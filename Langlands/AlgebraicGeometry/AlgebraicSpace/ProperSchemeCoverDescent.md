# Descending a supplied proper scheme cover to an actual affine stage

This internally derived unit descends an actual scheme cover of the limit
space, including eventual geometric surjectivity. Its main theorem assumes
a supplied cover; it does not assert cover existence for every space.

`ProperSchemeCoverAtStage` records an index in the actual original affine
diagram, a scheme over that stage with proper locally finitely presented
structural morphism, and a represented geometrically surjective map into the
stage base change of the given space. `isRepresentableMorphism_of_sourceIso`
uses an isomorphism to a scheme source and the target algebraic space's
representable diagonal to prove representability of any such morphism.

`exists_properSchemeCoverAtStage_of_limit_cover` assumes a quasi-separated
space with a quasi-compact locally finitely presented atlas over an affine
base and a compatible cofiltered affine diagram with its actual limit. Its
additional data are a scheme U over the limit, a represented geometrically
surjective map from U to the limit space, and properness and local finite
presentation of U over the limit. The conclusion is a
`ProperSchemeCoverAtStage` for some original diagram stage.

The proof first applies `exists_properSchemeStageModel` to descend the proper
scheme source. Its whole-space comparison turns the given cover into a map
between two limit base changes of stage spaces. On the incoming slice diagram,
`SpaceLimitUniqueness.exists_rebase_map` descends that morphism; its canonical
comparison equation transfers surjectivity to the literal limit base change.
The source is already a base change of a scheme, hence the descended map is
independently representable. The earlier
`isSurjective_limit_iff_of_representable` theorem detects its surjectivity at
a further incoming stage. Canonical scheme and iterated-base-change
isomorphisms produce an actual scheme cover over that final original stage.
Its structural morphism remains proper and locally finitely presented by
scheme base-change stability.

`exists_structuralUniversallyClosed_of_properSchemeCover` takes the independent
`ProperSchemeCoverStatement` as an explicit hypothesis. If the limit space's
structural morphism is proper, that hypothesis supplies the cover. The main
theorem descends it; `isUniversallyClosed_structural_of_scheme_cover` reflects
scheme universal closedness through its geometrically surjective map. Thus
some stage space has universally closed structural morphism.

The provenance is internal: the proper scheme stage model, published morphism
descent and base-change coherence, independently represented eventual
surjectivity, and surjective-source universal-closedness reflection. Integration
follows `ProperSchemeStageModel`, `RepresentedSurjectivityLimitDescent` and
`UniversallyClosedSourceCover`. The scheme-cover existence proof remains an
explicit unresolved prerequisite, and this unit alone does not establish the
full eight-property limit theorem.
