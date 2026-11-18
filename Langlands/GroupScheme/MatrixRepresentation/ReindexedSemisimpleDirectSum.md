# Semisimplicity of reindexed direct sums of actual representations

This internal linear-algebra module concerns the existing actual group-scheme
matrix representations and their all-affine-test stable subspaces. An injective
intertwiner from a nonzero simple representation has nonzero simple stable
image. `Intertwines.simple_range` applies the published
`IsIrreducible.isSimpleStableSubspace_range` to the given simplicity hypotheses.

The module uses `directSum_affineMatrix_val` from `SemisimpleDirectSum`
for the block diagonal affine test matrix. It supplies injective equivariant
coordinate maps from each block. These facts use the existing all-scheme-test direct sum and
its compatibility with affine matrices. The reindexed block injections contain every coordinate basis vector. The
simple-image lemma shows that their ranges are simple stable subspaces, and
the coordinate basis expansion shows their sum is the whole space. Thus a
finite direct sum of nonzero simple representations, reindexed along any
finite equivalence, satisfies the exact supremum-of-simple-subspaces
semisimplicity predicate. Empty families and empty coordinate sets are
included. All coefficient algebras, including
nonreduced ones, are retained.

Provenance: internal consequences of the Library's stable-subspace,
intertwiner, finite direct sum and reindexing constructions. These are auxiliary
linear algebra for the composition-factor route to Milne, *Algebraic Groups*
(2017), Proposition 21.60 (a) implies (d).
