# Local restrictions on finite Cartan matrices

`Langlands.LinearAlgebra.FiniteCartanLocalStructureStatement` is an internal
collection of consequences of Mathlib's `Matrix.IsFiniteCartan`, intended for
the exact finite Cartan enumeration. It quantifies over all finite index types
at universe `u`; the principal-submatrix index type has independent universe
`v`. No nonemptiness or indecomposability hypothesis is required.

It states four conclusions for an integral finite Cartan matrix `M`:

1. Restriction along any injective map from a finite index type remains finite
   Cartan.
2. Every nonzero vector of nonnegative integers has an index where both its
   coordinate and the corresponding coordinate of `M *ᵥ x` are positive.
3. For distinct indices the ordered entries are exactly one of
   `(0,0)`, `(-1,-1)`, `(-1,-2)`, `(-2,-1)`, `(-1,-3)`, or `(-3,-1)`.
4. In every row the sum of the edge products `M i j * M j i` over `j ≠ i`
   is at most three.

The second conclusion will exclude affine subdiagrams using explicit
nonnegative vectors. The last two preserve the orientation and multiplicity
of each edge. These restrictions alone do not classify the whole matrix.

The provenance is internal: these are elementary consequences of the positive
integral symmetrizer in `Matrix.IsFiniteCartan`, isolated as intermediate
obligations for the published exact classification target. This module states
the obligations and does not prove them.
