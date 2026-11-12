# Properness descent reduced to independent proper scheme covers

This internally derived unit proves the full properness limit clause with one
explicit foundational input, `ProperSchemeCoverStatement`. It also assembles
all eight original clauses conditional on that input and
`RepresentedAtlasEffectivityStatement`. Neither foundational proposition is
proved by this unit, so the unchanged host statement remains unproved until
those inputs are supplied by independent proofs.

The preliminary lemmas transport separatedness and properness through actual
isomorphisms of arrows. For separatedness, the proof uses isomorphism invariance
of the relative closed-immersion diagonal property; properness then combines
that result with the published quasi-compactness, local-finite-type and
universal-closedness transports. Structural universal closedness transports
through space isomorphisms and scheme base change by terminality of the base
presheaf, and structural separatedness is similarly preserved.

`structuralPullbackSymmetrySpaceIso` is the canonical comparison between the
two orders of a scheme pullback, retaining the same structural family.
`structuralUniversallyClosed_pullbackSymmetry_iff` applies base-change
preservation along the pullback symmetry and its inverse, followed by the
iterated-base-change isomorphism, to compare the two structural predicates.

`exists_proper_baseChange_of_separated_of_schemeCovers` starts with
separatedness at the original stage and properness at the limit. Choose an
affine finite-presentation etale surjective target atlas and its actual family.
The family is quasi-separated and has a finite-presentation atlas. Its
structural morphism is separated by the actual cartesian-square and rebase
comparisons. Over the incoming slice, use the actual target-chart pullback
diagram and its actual limit cone. The arbitrary-base-change target-family
criterion transfers limit universal closedness to its limit structural family;
pullback symmetry puts this on the diagram's actual limit scheme. Structural
separatedness and the finite-type atlas reductions make this limit structural
map proper. The supplied cover theorem and `ProperSchemeCoverDescent` then
give structural universal closedness at an actual incoming stage. The same
family comparison returns universal closedness of the stage morphism, and
the original separatedness plus finite-type reductions give stage properness.

`spaceLimitProperDescent_of_schemeCovers` removes original-stage separatedness
by first applying the independently published full separatedness descent
clause to the proper limit map. Work with that incoming separated stage and
transport limit properness through the canonical iterated-base-change
isomorphism. The preceding theorem gives a further proper stage; composition
of the incoming arrows returns a stage for the original map. Conversely, a
proper stage pulls back to the limit and transports through the same canonical
comparison. This proves exactly `SpaceLimitPropertyDescends` for the published
properness predicate, subject only to the displayed cover-existence input.

Finally, `spaceLimitPropertyDescent_of_foundations` has conclusion exactly
`SpaceLimitPropertyDescentStatement.{u}` and two explicit hypotheses:
`RepresentedAtlasEffectivityStatement.{u}` and
`ProperSchemeCoverStatement.{u}`. It uses public model uniqueness to discharge
the uniqueness inputs of the four represented-property reductions, the
conditional properness clause above, and the independently published full
separatedness, smoothness and nonempty-geometrically-connected-fibre clauses.
There is no extra host hypothesis or alteration of the original target pair.
This conditional reduction does not constitute an unconditional host proof.

The provenance is internal: actual target-family topology comparisons,
scheme-cover descent, scheme base-change coherence, the published separatedness
clause and finite-type reductions, and the existing represented-property and
connected-fibre results. Integration follows `ProperSchemeCoverDescent` and
`AffineTargetFamilyUniversallyClosedBaseChange` and their dependencies. The
foundational proofs belong to Task5472 (effective represented-property descent)
and Task5586 (proper scheme covers). Their acceptance and publication, followed
by an independently reviewed exact host proof, remain required.
