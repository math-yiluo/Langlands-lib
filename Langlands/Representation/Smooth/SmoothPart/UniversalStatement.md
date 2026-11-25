# Unique factorization through the smooth part: proposition target

`Langlands.SmoothPartUniversalProperty` is a proposition definition.
For any topological group `G`, commutative ring `R`, independently universed
`R`-modules `V` and `W`, representations `rho` on `V` and `sigma` on `W`, and
smoothness proof for `sigma`, every intertwiner `f : sigma -> rho` has a unique
intertwiner `lift : sigma -> smoothPart rho` whose composite with the inclusion
is `f`. The uniqueness quantifies equality of the bundled intertwiners.

The topological-group instance is explicitly quantified inside the proposition.
No admissibility, finite-generation, local-compactness, or topology on either
module is assumed. The only project import is the
`SmoothPart.Definitions` module and its foundational dependency.

This is an internal universal property of the smooth-vector subspace described
by Casselman, not a quotation of a separately numbered result. Equivariance
makes the image of a smooth representation consist of smooth vectors; subtype
inclusion makes the factorization unique.

Source: `casselman-2019-smooth-representations`, content SHA
`2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`,
Chapter II, revision June 16, 2019, Section 1, page 2, first two paragraphs.
See [Definitions](Definitions.md) for the original file, precise construction
and dependency versions, and pinned environment.

The topological-group instance is placed in the proposition itself, rather
than as an external declaration parameter, so the whole
assumption is visible in the target.
The direct construction dependency is
`Langlands.Representation.Smooth.SmoothPart.Definitions`. Its transitive
foundation is `Langlands.Representation.Smooth.Definitions`.

`UniversalProof.lean` implements the entire target as
`Langlands.smoothPartUniversalProperty`, introducing the topological-group
instance at its internal binder. The canonical lift supplies existence, and
subtype and intertwiner extensionality supply uniqueness. The statement defines
the proposition; the separate proof establishes it.

## Checks

The proof's validation reports successful exact-target checking, beyond
source presence and development compilation.
