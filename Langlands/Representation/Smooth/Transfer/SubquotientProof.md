# Smoothness transfer along intertwiners

This module proves `Langlands.SmoothSubquotientStatement`
from the adjacent statement module.

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
The original June 16, 2019 PDF was read at pages 1, 2, and 4, and
the source fingerprint was verified. The proof implements only smoothness inheritance,
not the following assertion of exactness on compact-open fixed vectors.

The exact target is the statement `Langlands.SmoothSubquotientStatement`.
Its proposition fingerprint is
`274536c672c0e34b74eaa7b7a89b524a70c774ed75c2ee52212337b419b8a02a`.
The statement and its sole project definition dependency
`Langlands.Representation.Smooth.Definitions` were checked to be
available; the local statement pair matches the recorded bytes.
The definition has Lean SHA256
`435abfa2c0b05c1b6ea8107e3278687e7091e481540508d6647befc0f515aabb`.
The module `Langlands.Representation.Smooth.Transfer.SubquotientProof` and its
closing theorem `Langlands.smoothSubquotient` prove this exact target in
the pinned environment. Native compilation supplies development evidence.
This file makes no claim of the full local Langlands correspondence.

Environment: Lean 4.34.0 at `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`,
Mathlib at `5ed2965256430c3649e86755f9576b54eca72435`.
