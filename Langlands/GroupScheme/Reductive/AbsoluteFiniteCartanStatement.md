# Finite indecomposable Cartan matrices on actual absolute vertices

This is an internal intermediate statement for the exact absolute Cartan
classification of actual absolutely almost-simple groups. It isolates the
actual-group input from the generic enumeration of finite Cartan matrices.
Its provenance is the published
`AbsolutelyAlmostSimpleCartanClassificationStatement` and the existing actual
Tits-index interface, rather than a new translation of a literature statement.

For any `TitsIndexData G`, `TitsIndexData.HasFiniteIndecomposableCartan` says
that the entire type `d.Vertex` is nonempty and the matrix whose entries are
exactly `d.cartan a b` is finite Cartan and indecomposable, using Mathlib's
`Matrix.IsFiniteCartan` and `Matrix.IsIndecomposable`.
The finite enumeration and decidable equality used to formulate the first
matrix predicate are chosen classically from the already published finiteness
of the actual vertex type.

In particular, finite Cartan means diagonal entries two, nonpositive
off-diagonal entries, symmetric vanishing, and an integer diagonal
symmetrizer with positive entries whose product with the Cartan matrix is
positive definite. Indecomposability rules out a permutation into a block
triangular matrix with two nonempty blocks.

`AbsolutelyAlmostSimpleFiniteCartanStatement.{u}` asserts this property for
every field in universe `u`, every affine locally finite type group scheme,
and every supplied actual Tits index, under absolute almost-simplicity.
It has no characteristic or local-field restriction. It asserts no family
enumeration, numbering, marking, or Galois-action classification. The statement
is a proof obligation; this file does not prove it.
