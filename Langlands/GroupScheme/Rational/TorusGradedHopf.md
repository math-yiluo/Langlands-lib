# Integer graded coordinate algebras from actual torus actions

This internal bridge uses the actual split-torus action on a group scheme over
an arbitrary field in any universe. It coarsens the coordinate character decomposition along a
cocharacter avoiding the finite cotangent support. The absence of the zero Lie
weight excludes the zero cotangent weight by the published support comparison.
Every augmentation element in degree zero then belongs to the square of the
augmentation ideal. Affineness of the structure morphism and local finite type
suffice for this construction; smoothness and connectedness are not premises.

`exists_coordinate_grading` constructs this integer grading on
`CharacterUnits.Coord H`. It proves multiplication compatibility through
`gradedAlgebraRegrade`, comultiplication compatibility through `regrade_comul`,
counit vanishing in nonzero degrees, and the degree-zero square condition through
`regrade_zero_mem_sq`. A character whose coarsened degree is zero lies outside the
cotangent support, so its augmentation part has zero cotangent class. The
regrading lemma handles sums with cancelling scalar parts. The construction
also allows an empty cotangent support and a torus of rank zero. These reused
helpers are due to Workers 1388 and 1398.

`pullGrading` and `gradedAlgebraPull` transport a grading along an algebra
equivalence. `iSup_map₂_le_tensorGrade` relates the coordinate API's sum of
bilinear images to the total-degree tensor span of `GradedHopf`.
`exists_grading_of_coordinate_equiv` transports the coordinate grading to a
bialgebra when the equivalence preserves comultiplication and counit. It maps
the tensor span through the inverse equivalence, and transports augmentation
ideal squares by the inverse ring equivalence. This transport works for
commutative algebras in independent universes over a field. Only the source
algebra needs a bialgebra instance: the target supplies explicit algebra maps
for comultiplication and counit and their compatibility with the equivalence.

This is an internal composition of the existing coordinate decomposition,
cotangent support comparison, generic cocharacter, regrading and graded-Hopf
interfaces. Worker 1324 wrote the coarsening and transport composition. The
unchanged supporting `TorusUnipotence/` pairs retain Workers 1388 and 1398
authorship. They are included as dependencies while their independent
publication is pending. The present entry module introduces no new external
source assertion.

This unit does not assert split unipotence. The actual coordinate-Hopf comparison
is a separate input to the transport theorem; identification of chosen coordinate
presentations and assembly of the host semigroup-realization target remain
consumer obligations.
