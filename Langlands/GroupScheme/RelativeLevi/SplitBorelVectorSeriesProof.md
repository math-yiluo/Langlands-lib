# Split Borel structure with a finite affine vector-quotient kernel series

Authors: Worker 591 and Worker 686. The generic represented root-height
construction is by Worker 204.

`splitBorelVectorSeries` proves the unchanged Library proposition
`Langlands.GroupScheme.SplitBorelVectorSeriesStatement.{u}` for every universe.
It retains every commutative ring, including the zero ring, and exactly the
specified reductivity, closed fibrewise maximal coordinate torus, common
fibrewise root datum and free rank-one actual root-weight hypotheses.

The proof first uses
`LocalRootGroup.rootParametrizationsOfFreeWeights` to choose actual global
additive root parametrizations. Their correctness theorem supplies actual
root-subgroup representation and all-test torus equivariance. The assembly
then constructs a `SplitBorelPositiveChart` and its root-height chart on the
actual regular contracting group.

The supporting `RootHeightChart.hasFiniteAffineVectorSeries` constructs the
required affine vector-quotient series directly from represented height
terms. At each positive height the actual quotient is the standard vector
group indexed by roots of that height. Its map is flat, surjective and locally
of finite presentation, with the actual scheme-kernel range equal to the
next closed subgroup on every scheme test. The finite maximum of the positive
heights bounds the series. The next term is trivial on every test, and the
height-one group-scheme isomorphism transports the series to the actual
contracting group. This also covers empty root families and missing heights.

Finally,
`AffineRegularBorel.hasSplitBorelVectorSeries_of_contractingSeries` supplies
the relative Borel containing the original coordinate torus, its affine
closed contracting kernel, the split projection to the original torus and
its represented fppf quotient with the exact all-test kernel identity.
The chart's regularity field is its required nonzero root-pairing premise.
No Borel or series is an input to the final theorem. The proof imposes no
connectedness, reducedness, localness, field or nonzero-ring hypothesis.

This is a derived composition of the indicated Library constructions.
The paired assembly Markdown explains the affine-series recursion and
isomorphism transport. The proof uses group-scheme isomorphisms only where
they have been proved; the positive-root product chart itself is a scheme
isomorphism and does not identify the noncommutative group law with addition.
