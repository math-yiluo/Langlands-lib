# Trivial actual actions and their semigroup subgroups

This internal unit constructs `AutomorphicAction.trivial` over any base scheme
and universe. Its action morphism is the second projection. The product
identities prove its action laws and its evaluation on every test scheme.
An actual action fixing every point on every test equals this construction:
evaluate at the universal pair of projections to identify its morphism.

For a pointwise trivial action of a commutative group scheme over a field,
every Lie vector has character weight zero. This follows directly from the
intrinsic eigenvector condition, the value one of the zero character, and
the identity law for epsilon scaling. If the acting group is a split torus
and the affine target is locally of finite type, independence of its actual
character weight spaces makes every nonzero-character weight space zero.
The support of every subgroup functor is therefore contained in `{0}`.
Zero need not occur: the Lie algebra may itself be zero.

For such a trivial action, any positive additive semigroup excluding zero
has identity semigroup subgroup on all tests, by the existing theorem for
absence of ambient weights. If the ambient group is also smooth and
connected, any semigroup containing zero has the entire group as its
semigroup subgroup, since the group itself is an admissible generator.
Thus in this smooth connected case the exact functor is top or bottom
according to membership of zero in the given semigroup. The argument
does not insert zero into positive additive generation.

The provenance is internal: the actual projection action, intrinsic
eigenvectors, the published split-torus weight independence, and the
existing no-ambient-weight and covering-support semigroup theorems.
No semigroup realization or solvable decomposition is assumed or proved.
