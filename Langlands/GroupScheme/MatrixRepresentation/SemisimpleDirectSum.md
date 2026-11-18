# Simple subspaces and semisimplicity of actual direct sums

This derived construction supports the finite direct-sum step of the published
`SplitHighestWeightBaseChangeStatement`, Task 7109. It uses the published actual
direct-sum representation and all-affine-test stability. Its results are linear
algebra consequences of those interfaces; it does not introduce a new
representation-theoretic hypothesis.

`directSumInclusion` is the matrix of the canonical inclusion of a coordinate
summand, defined using dependent-function currying and a linear single map.
Its action extends a vector by zero; it is injective, is preserved by scalar
extension, and its images span the whole sum. The affine matrices of the
actual direct-sum representation are block diagonal. The affine formula follows
from the published point-matrix formula by the affine sections algebra
equivalence. A block matrix acts separately on each summand, which proves that
the canonical inclusion intertwines the corresponding actual representations
on every affine algebra test.

`IsSimpleStableSubspace` and `IsSemisimple` name the exact simple-subspace and
sum-of-simple-subspaces formulas used in the published highest-weight
base-change statement, for arbitrary finite coordinate types. The image of a
simple stable subspace under an injective intertwiner is simple and stable:
stability is equivariant image stability, nonzeroness follows from injectivity,
and minimality follows by pulling a stable subspace back to the domain. The
corresponding result for the whole space of an irreducible representation is
also proved.

A bijective actual intertwiner transports semisimplicity. Each simple
subspace maps into the supremum of the target's simple subspaces, and
surjectivity makes the image of their span the whole target.

Finally, a finite direct sum of irreducible representations is semisimple.
Each canonical inclusion has a simple stable image, and every vector is the
finite sum of its coordinate-summand components. This includes an empty
family, whose zero coordinate space is semisimple by the same argument.
The module does not assert classification of simple representations or
semisimple descent.

`IsSemisimple` is reused from `StableComplements`. Its formula agrees
definitionally with the sum over `IsSimpleStableSubspace` used here.
