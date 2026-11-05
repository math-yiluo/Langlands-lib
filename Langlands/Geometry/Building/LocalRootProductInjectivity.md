# Ordered root products from local opposite factor pairs

Worker 1302, adapting Worker 1315's published assembly argument and local
interface guidance. This internal construction defines
`RelativeRoot.orderedRootSubgroupProductEmbeddingOfFactorPairs`. Its underlying
function multiplies the actual relative-root subgroup points in the supplied
order on every scheme test.

The group is smooth and affine over any field in arbitrary universe `u`.
The map `i` is a monomorphic map from a split torus. The sole additional
structural premise is `HasOppositeFactorPairs i` for this particular map.
An arbitrary cocharacter and any injective finite enumeration of its
indivisible positive actual roots are allowed. No connected reductivity,
maximal splitness, generic cocharacter, nonempty root set, or reducedness
premise is imposed.

The proof localizes the positive-semigroup argument of the published
`DynamicRootProductAssembly`. Semigroup realization gives a smooth connected
closed representative of the positive conjugation semigroup. Its weight
support is exactly the positive relative roots and positivity excludes the
zero character, so the representative is unipotent. Local pair existence
supplies disjoint positive integral rays through distinct indivisible roots
via `HasOppositeFactorPairs.disjoint_cyclicTail_indivisibleRoots`.
The existing unconditional coverage result partitions the positive support
into actual-root ray blocks. The arbitrary-field unipotent product theorem
therefore gives representing factors with isomorphic ordered multiplication
inside the positive representative.

Equivariant transport along its closed inclusion identifies each factor's
ambient subgroup with the first cyclic-tail subgroup. The published
`cyclicRootFunctorComparison` identifies it with the actual root subgroup.
Postcomposition of the isomorphic internal multiplication with the monic
inclusion is the ambient ordered multiplication. The existing
`orderedSubgroupPoints_injective_of_mono` then gives injectivity on every test.
The displayed embedding uses exactly that multiplication function.

The provenance is this internal specialization of published semigroup
realization, unipotent products, ray separation, cyclic comparison and
represented-point arguments. It establishes neither opposite-pair existence
nor the global `DynamicRootOrderedProductStatement`. It does not use a global
ray-decomposition or Dynamic-product proposition as a premise.
