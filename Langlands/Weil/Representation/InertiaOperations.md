# Operations on representations with open inertia kernel

Worker 17 authored this construction module. It compiles without warnings
or errors; independent semantic acceptance and publication remain required.
It imports the separate inertia predicate and the actual finite-representation
operations. Its group has an explicit topological-group structure; inertia
is any supplied subgroup with its subgroup topology. No compactness or
normality of inertia is required for these certificates.

This contribution includes the paired `Invariants`, `Restriction`,
`SumsTensor`, `Dual`, `Twist` and `Determinant` modules in this directory.
They construct operations on actual carriers, their maps and functors where
applicable, actual representation equivalences, and well-defined operations
on genuine isomorphism classes. The present module proves the certificates
needed to restrict the algebraic operations to open-inertia objects.
`Restriction` supplies algebraic precomposition; its topological parameter
restriction is a separate construction.

The published imports are `Langlands.Weil.Representation.Basic`,
`Langlands.Weil.Representation.Predicates`,
`Langlands.Representation.Dual.Definitions` (Worker 0), and
`Langlands.Representation.Twist.Definitions` (Worker 4), in Library commit
`843c574c920aa9926ab56adf662c74b3cd4ed0e1`. They are imported without copying
or changing their source. The included operation modules are Worker 17's.

An injective intertwiner transfers trivial action from its target to its
source. The target inertia kernel is therefore contained in the source
kernel. An open subgroup contained in another subgroup makes the latter
open, by Mathlib's `Subgroup.isOpen_mono`. This supplies a reusable
certificate for later invariant and monodromy-kernel constructions.

The kernel for a sum or tensor contains the intersection of the two
original kernels. For the algebraic dual, an original kernel element and
its inverse act trivially. For a character twist, intersect the original
kernel with the explicitly assumed open kernel of the character restricted
to inertia. For the determinant, an identity action has determinant one.
These arguments prove all open-kernel certificates used by
`openInertiaSum`, `openInertiaTensor`, `openInertiaDual`,
`openInertiaTwist`, and `openInertiaDeterminant`. The same injective
inclusion argument supplies `openInertiaInvariants` for any normal subgroup.

These are actual constructors on the specified object subtypes. They
do not assume that continuity implies an open kernel, that inertia has
finite image, or that semisimplicity is preserved. Those are distinct
predicates and theorem obligations.

Source correspondence: Tate, *Number theoretic background*, Corvallis
Part II, §4.1.2 and §4.1.5, printed page 20, supplies the open-inertia
convention and algebraic pair operations. The preservation certificates
here are elementary derived obligations of those operations; they are
proved directly by subgroup-kernel inclusions and openness. Source ID
`tate-1979-number-theoretic-background`, PDF SHA-256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
