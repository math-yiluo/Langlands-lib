# Actual semigroup generators depend only on occurring weights

This internal unit combines the actual support monotonicity in
`Rational.SemigroupClosure` with the exact cross-exclusion identity in
`Rational.SemigroupPartition`. Its proofs are elementary consequences of
those published constructions. It introduces no geometric premise.

`weightSupportedGenerators b Ξ` is the family of smooth connected closed
subgroup functors that are stable under the actual action and whose actual
intrinsic Lie weights lie in the specified character set `Ξ`. This is an
auxiliary set of generators; the actual subgroup functor throughout remains
the published `semigroupSubgroup`.

The support of every subgroup functor lies in total ambient support:
support monotonicity carries the same nonzero tangent vector through the
inclusion in the top subgroup functor. Consequently a bound by `Ξ` is
equivalent to a bound by `Ξ` intersected with total support. Removing
nonoccurring characters therefore preserves the family of generators.
The family is also monotone in the character bound, and its specialization
to a semigroup is exactly the published `IsSemigroupGenerator` predicate.

For a covering partition with the exact original-block versus
other-generated-semigroup exclusion, `closure_inter_support` identifies
each generated semigroup's intersection with total support with its
original block. Rewriting the generator-family equality proves that the
canonical factor's admissible generators are exactly the smooth connected
closed invariant subgroup functors whose weights lie in that original
block. `semigroupSubgroup_closure_carrier` expresses this equality inside
the existing subgroup closure on every test scheme.
`semigroupSubgroup_closure_le_iff` likewise rewrites the published all-test
universal property: a factor lies in a subgroup functor exactly when every
smooth connected closed invariant subgroup supported in that original
block does.

The field universe and the partition index universe are independent.
No nonempty index hypothesis is imposed, and the positive
`AddSubsemigroup.closure` convention is unchanged. Zero is treated like
every other occurring weight. These results neither require nor establish
pairwise disjointness of the generated semigroups. They do not prove a
support bound on a generated subgroup, smooth representability, an exact
Lie image, or an ordered multiplication isomorphism.
