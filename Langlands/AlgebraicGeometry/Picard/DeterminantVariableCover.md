# Comparison of variable-rank determinant lines across covers

This derived internal construction compares determinant lines for two covering
families of actual local frames of the same module sheaf. Each frame has a
supplied finite rank, and ranks may vary both within and between families.
The schemes and chart index types are in the same universe. The source of
`lineBundleCoverChangeIso` is the determinant line from the first family;
its target is the determinant line from the second family.

A selected subfamily has the refined cocycle. Its existing determinant
generators form a frame with those transitions. When this subfamily covers,
`reindexIso` identifies the actual glued sheaves, carrying each selected
local determinant generator to its counterpart.

`sumFrames` combines both families on the disjoint union of their index types,
using the corresponding disjoint union of the rank functions.
`coverChangeIso` compares the original presentations through this common
family. On every open inside a chart of each cover, its generator formula is
the mixed finite-basis determinant that expresses the first frame in the
second frame. This includes unequal ranks, which force a trivial section ring.

The mixed determinant identity and composition laws give the corresponding
laws for cover comparison. The composition proof checks the actual maps on
sections over the triple-intersection cover: every section is a scalar
multiple of its determinant generator, so the generator formulas and mixed
unit composition suffice. The sheaf isomorphisms lift to actual line bundles
through the full subcategory of locally free rank-one module sheaves.

The proof extends the existing constant-rank cover-comparison argument using
`VariableDeterminantFrames` and `FiniteBasisDeterminant`. It supplies cover
comparison and its identity and transitivity laws, while leaving functoriality
under module isomorphisms, pullback coherence, finite frame existence and
parabolic polarization as separate obligations.
