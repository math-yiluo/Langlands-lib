# Unit correction of actual scalar-extended pinning vectors

Let two supplied affine pinned models be extended to an arbitrary common
commutative coefficient ring. An actual isomorphism of their groups, an actual
isomorphism of their coordinate tori with its inclusion square, and a
bijection of the simple-root supports with actual character alignment give
a unique family of units describing the discrepancies between the actual
scalar-extended chosen pinning vectors. All alignment data are premises.

This specializes the aligned weight-line equivalence and its unique-unit
theorem to the models' scalar-extended pinning trivializations. Choice assembles
the unique units into a function on the original source simple-root support;
pointwise uniqueness proves uniqueness of that function. The coefficient ring
need not be a field, local ring, reduced ring, or nonzero ring.
`pinningUnitDiscrepancies` selects this unique function, and
`pinningUnitDiscrepancies_spec` gives its actual differential equation.

Given those discrepancies, a supplied actual target coordinate-torus section
whose simple-root values are the inverse units corrects every chosen vector.
The proof applies the actual inner differential formula from
`Lie/InnerAdjoint` to each target weight vector. It also translates the
differential equations into equalities of the original models' actual
dual-number pinning points on this coefficient test, using the published
scalar-extension pinning-point identities.

This is an internal specialization of `AlignedWeightLineUnits`,
`AffinePinnedScalarExtension`, and the bundled `Lie/InnerAdjoint` deduction.
It does not construct root alignment or a torus section realizing the
prescribed values. It asserts equations on the supplied common coefficient
ring and does not itself assert the all-local-tests pinning predicate or the
parent comparison-existence theorem.
