# Ordered products from solvable intersections

This internal construction narrows central-vector induction to inverse images
whose source is solvable. It assumes the independent
`Torus.SolvableFixedContainmentConnectedStatement` and
`CentralStableVectorSubgroupStatement`. Neither premise is proved here, and the
full arbitrary-field ordered product statement remains open.

`semigroup_comap_eq_of_solvable` works over any field in universe `u`. Its
ambient group is smooth affine, and its closed subgroup is smooth, connected,
affine and uniformly solvable on all scheme tests. The two actual split-torus
actions commute with the supplied inclusion. For every additive semigroup
`A`, the inverse image of the ambient semigroup subgroup equals the subgroup's
own semigroup subgroup. If zero belongs to `A`, the published solvable
comparison applies with the explicit fixed-containment connectedness premise.
If zero is absent, the published zero-excluded comparison applies with the
proved coordinate/Lie containment. Both cases use the published semigroup
realization theorem. No general normal-subgroup intersection statement is
assumed.

`isSolvableScheme_of_vectorCoordinates` uses the actual multiplicative point
equivalences supplied by the central-vector premise. On every test scheme,
the target of this equivalence is the additive group of a finite free module over
the ring of global functions, written multiplicatively. It is commutative,
so its first derived subgroup is trivial. Injectivity transfers that same
bound one to every point group of the vector subgroup. No linearity or
naturality is needed for this solvability argument.

`unipotentSemigroupOrderedProduct_of_solvableIntersection` proves the exact
algebraically closed unipotent statement by strong induction on smooth
relative dimension. The all-test trivial group is the base case. Otherwise
the explicit central-vector premise supplies a positive-dimensional smooth
connected closed central stable subgroup with actual linear coordinates.
The published affine-orbit and unipotent normal-quotient theorems supply its
actual equivariant smooth fppf quotient, still smooth connected affine
unipotent and of smaller relative dimension. The vector ordered product
theorem handles the central subgroup, and induction handles the quotient.
The local central-extension assembly theorem then uses the solvable inverse
image equality just proved. Thus the general intersection statement is
unnecessary in this induction. Realization, coordinate containment and smooth
quotient comparison are supplied by published proofs.

`solvableUnipotentOrderedSemigroupProduct` chooses actual factors from this
theorem for one supplied ordered family. It returns the existing
`OrderedSemigroupProductData`: group schemes, inclusions representing the
actual semigroup functors, smooth connected closed geometry, and a scheme
isomorphism whose forward map is the original ordered multiplication.
Its field is algebraically closed and its ambient group smooth connected
affine unipotent. The complete occurring Lie support includes zero when it
occurs; semigroups are positive `AddSubsemigroup.closure`s. The assumptions
remain disjoint original blocks and exclusion of each original block from
every other block's generated semigroup. No disjointness of generated
semigroups is used. Arbitrary orders and the empty family are retained.

The proof is derived from the imported constructions and explicit premises.
It adapts the existing central-vector induction authored by Worker 1313 and
Worker 362, preserving Worker 362's central-vector existence scope.
