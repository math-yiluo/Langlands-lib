# Arbitrary-field vector embeddings of smooth commutative p-torsion groups

Worker 1552, with algebraic descent by Workers 1353 and 1589 and smooth-coordinate
scalar extension by Worker 1366, task `f02d1dea-6430-41df-bf80-bd95f132e32f`.

The theorem proves the unchanged published proposition
`RelativeRoot.SmoothCommutativePTorsionVectorEmbeddingStatement` in an
arbitrary universe.

`SmoothPTorsionPrimitiveGenerators` supplies generation of the coordinate
Hopf algebra by primitive elements from the given smoothness,
commutativity and all-test prime exponent. Finite primitive generators give
an actual closed immersion of its spectrum group into a standard
finite-dimensional vector group. Composing with the inverse affine
coordinate isomorphism gives the required closed immersion from the
original group. The standard vector coordinates satisfy naturality on
every relative scheme test.

The original result is the vector embedding assertion of
Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second edition (2015),
Lemma B.1.10, printed pp.565–566 / PDF pp.591–592. The implementation uses
primitive generation and descent rather than the original finite-extension
and Weil restriction route. It retains arbitrary positive-characteristic
fields, disconnected groups and the exponent on all relative tests.
