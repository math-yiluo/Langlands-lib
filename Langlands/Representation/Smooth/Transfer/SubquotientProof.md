# Smoothness transfer along intertwiners

Worker 0's implementation proves `Langlands.SmoothSubquotientStatement`
from the adjacent accepted statement module. Worker 11 checked the implementation
and prepared its proof submission and documentation.

`mem_fixedVectors_iff` unfolds the fixed-vector submodule as invariants
of the restricted action. Its equivalence is definitional.

`isSmoothVector_map` chooses an open subgroup fixing a vector and uses
equivariance to show that the same subgroup fixes its image.
`isSmoothVector_of_injective` starts with an open subgroup fixing the
image, then uses equivariance and injectivity to obtain the fixing
equation before applying the map. `isSmooth_of_injective` applies that
argument to every vector. `isSmooth_of_surjective` chooses a preimage
of each target vector and applies `isSmoothVector_map`.
`smoothSubquotient` introduces both representations and their intertwiner,
then packages the two resulting implications as the complete target conjunction.

The ring, group, source module, and target module have independent universes.
The assumptions are exactly a commutative ring, a group with a topology, and two
modules; there is no continuity assumption on the group operations or topology
on either module. The fixing subgroup can depend on the vector. The purely
algebraic lemma `mem_fixedVectors_iff` omits even the topology on the group.

No averaging, Haar measure, invariant-vector exactness theorem, or
coefficient division is used. This explains the hypothesis generalization
recorded in [SubquotientStatement.md](SubquotientStatement.md).

The source is Casselman, Chapter II, Proposition II.1.3, page 4,
smoothness clause only; `literature_id`
`casselman-2019-smooth-representations`, SHA256
`2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`.
The adjacent statement Markdown gives the precise original file,
quantifiers, generalized hypotheses, and exact definition dependency.
Worker 11 read the original June 16, 2019 PDF, pages 1, 2, and 4, and verified
the source fingerprint. The proof implements only smoothness inheritance,
not the following assertion of exactness on compact-open fixed vectors.

The exact target is accepted statement
`b838525e-4b0b-4f85-9085-6f384abedf7a`, version 1,
published at commit `184e47d712351b887a9792a4fda56c6491629c92` with
independent receipt `309a8d2a-3794-4d01-b3ab-c8d436d8c668`.
Its proposition fingerprint is
`274536c672c0e34b74eaa7b7a89b524a70c774ed75c2ee52212337b419b8a02a`.
The accepted statement and its sole project definition dependency
`665022df-625b-44ae-9dbd-425f6e266bab`, version 1, are currently
available; the local statement pair matches the effective reviewed bytes.
The definition is published at commit
`10c81beaaff024987cf2945c64d0c9511f6cb686`, with Lean SHA256
`435abfa2c0b05c1b6ea8107e3278687e7091e481540508d6647befc0f515aabb`.
Proof task `0975ce00-a7a0-4031-a31f-1df98f3afaf3`, revision 1, binds
module `Langlands.Representation.Smooth.Transfer.SubquotientProof` and
closing theorem `Langlands.smoothSubquotient` to this exact target and
the pinned environment. Native compilation supplies development evidence.
Independent checker, semantic-review, and publication receipts are recorded
separately; this file makes no claim of the full local Langlands correspondence.

Environment: `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1,
Lean 4.34.0 at `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`,
Mathlib at `5ed2965256430c3649e86755f9576b54eca72435`.
