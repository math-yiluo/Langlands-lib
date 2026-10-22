# Unique factorization through the smooth part: proposition target

`Langlands.SmoothPartUniversalProperty` is an unaccepted proposition definition.
For any topological group `G`, commutative ring `R`, independently universed
`R`-modules `V` and `W`, representations `rho` on `V` and `sigma` on `W`, and
smoothness proof for `sigma`, every intertwiner `f : sigma -> rho` has a unique
intertwiner `lift : sigma -> smoothPart rho` whose composite with the inclusion
is `f`. The uniqueness quantifies equality of the bundled intertwiners.

The topological-group instance is explicitly quantified inside the proposition.
No admissibility, finite-generation, local-compactness, or topology on either
module is assumed. The only project import is the accepted
`SmoothPart.Definitions` pair and its accepted foundational dependency.

This is an internal universal property of the smooth-vector subspace described
by Casselman, not a quotation of a separately numbered result. Equivariance
makes the image of a smooth representation consist of smooth vectors; subtype
inclusion makes the factorization unique.

Source: `casselman-2019-smooth-representations`, content SHA
`2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`,
Chapter II, revision June 16, 2019, Section 1, page 2, first two paragraphs.
See [Definitions](Definitions.md) for the original file, precise construction
and dependency versions, and pinned environment.

The previous aggregate draft used the same proposition name with its
topological-group instance as an external declaration parameter. This separated
target places that instance in the proposition itself so the whole
assumption is visible in the target. No accepted target is changed.
The direct construction dependency is artifact
`9fb5627f-6e8c-48a5-a92f-a4ddcf319b2d`, version 1, independently published at
Library commit `cd8210540c75a7d0a9e2431e4bc9a2535ceaf919`, with receipt
`1f969dc8-79b0-4e70-adf8-502752d70c6a`. Its transitive foundation is
`665022df-625b-44ae-9dbd-425f6e266bab`, version 1. Both pairs are currently
published and their local bytes match the effective reviewed versions.
This target is submitted for independent statement review; its proof requires
a separately bound proof task after target acceptance and publication.
