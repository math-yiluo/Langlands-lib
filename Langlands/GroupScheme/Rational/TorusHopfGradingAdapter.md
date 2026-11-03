# The actual Hopf grading for a torus action without zero Lie weights

For any field `k` in any universe, let `H` be a smooth affine group scheme,
let `S` be a split torus, and let `b` be an actual automorphic action of `S` on
`H`. Assume that `RelativeRoot.actionWeightSpace b 0` is zero.
`TorusGradedHopf.exists_graded_of_noZeroWeight` constructs an integer grading
on `AffineCoordinates.hopfAlgebra H`. It is a `GradedAlgebra`, its actual
bialgebra comultiplication preserves total degree, and its actual counit
vanishes on every nonzero degree. Every degree-zero element in the kernel of
that counit lies in the square of its kernel.

The proof installs the given smoothness as a local instance, supplying local
finite type. `exists_coordinate_grading` then gives the character-coarsened
grading on `CharacterUnits.Coord H`, including the zero-degree square
condition. `AffineCoordinates.lieCoordinateAlgEquiv H` compares the actual
coordinate Hopf algebra with this coordinate algebra. Its proved
`lieCoordinateAlgEquiv_comul` and `lieCoordinateAlgEquiv_counit` laws identify
the two comultiplications and counits. Applying
`exists_grading_of_coordinate_equiv` transports all the grading conclusions.
No independent choice of a replacement Hopf structure occurs.

`gradingOfNoZeroWeight` chooses such a family of subspaces.
`gradedAlgebraOfNoZeroWeight` gives its algebra grading, and
`gradingOfNoZeroWeight_spec` gives its graded bialgebra and augmentation-square
properties. Connectedness is not a premise. The explicit affineness
hypotheses match the interface used by the split-unipotence consumer.

This is an internal composition of the coordinate grading, compatible
coordinate comparison, and grading transport constructions. Worker 1324
assembled this adapter and the coarsening/transport bridge; Worker 1285
constructed the coordinate comparison, with Worker 1324 contributing its
identification route. The unchanged supporting torus-unipotence helpers retain
Workers 1388 and 1398 authorship. No new assertion is attributed to external
literature. This contribution supplies the actual Hopf grading prerequisite;
the split-unipotence and complete semigroup-realization conclusions remain
consumer obligations.
