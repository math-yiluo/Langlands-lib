# Action-compatible solvable factorization and exact semigroup reduction

This internal construction combines the actual external semidirect complement
adapter with the existing maximal-torus intersection and semigroup transport
interfaces. Its structural inputs remain explicit; it does not prove the
unconditional ordered-product target.

`FixedTorusUnipotentFactorization a` records actual factors of the original
group, their original inclusions, and invertibility of their actual subgroup
multiplication. The normal factor is affine, smooth, connected and unipotent,
its inclusion is closed, and its range is normal and stable under `a`. The
other factor is a smooth connected affine torus, closed in the original group
and fixed pointwise by `a` on every scheme test.

Over an algebraically closed field, `solvableFactorization` constructs this
record from `SolvableMaximalTorusSemidirectStatement`, for a smooth connected
affine uniformly solvable original group and a split acting torus.
The external semidirect product is affine and smooth. Geometric connectedness
of the normal coordinate makes its product with the connected acting torus
connected. The uniform solvability bound for a semidirect product supplies
the geometric solvability required by the structural input.

Choose an external maximal torus containing the acting torus. Its actual
scheme-theoretic intersection with the original group is already a smooth
connected closed affine torus fixed by the action. Apply the supplied
structural decomposition to the external group and that maximal torus.
The supplied unipotent factor projects trivially to the acting split torus,
so the external complement adapter constructs its inclusion in the original
group. Closedness follows from closedness of its composite with the closed
normal-coordinate inclusion, and affineness follows from this original closed
inclusion. External normality gives both original normality and action
stability. The adapter restricts the actual external multiplication
isomorphism to the actual original multiplication. Maximality of the
intersection inside the original group is not needed.

`semigroupSolvableReduction_of_maximalTorusDecomposition` proves the published
`SemigroupSolvableReductionStatement` under the structural decomposition
and full `SemigroupIntersectionStatement` premises. The exact algebraically
closed unipotent core applies to the action on the represented normal factor.
The existing subgroup-factorization theorem transfers its ordered products
to the original action. Published field-extension detection then descends the
property to an arbitrary field in the same universe.

`semigroupOrderedProduct_of_structuralInputs` also composes the existing
central-vector induction. Published realization, smooth-quotient comparison
and functoriality are used as theorems. It retains three explicit premises:
the structural maximal-torus decomposition, the full semigroup intersection
comparison, and central stable vector-subgroup existence. None of those
three premises is proved here. The result retains the complete occurring
weight support, including zero, positive additive-semigroup generation,
the exact block-versus-generated-semigroup exclusion, every ordering, the
empty index, and the original multiplication as a scheme isomorphism.

The provenance is internal: the construction and implications compose the
actual published semidirect maps, geometric connectedness, solvability
comparison, fixed torus intersection, subgroup factorization, scalar
reduction and central induction. No new structural existence assertion is
introduced as an axiom or supplied by an instance.
