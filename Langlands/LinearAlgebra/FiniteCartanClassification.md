# Finite Cartan classification by deleting a leaf

This development proves the exact generic finite Cartan classification by
induction on the finite number of vertices.

Indecomposability makes the underlying graph connected, and positive
definiteness makes it acyclic. In rank one every entry is two and the
matrix has type A1. In larger rank the diagram is a finite tree, so it
has a vertex of degree one. Deleting that vertex preserves connectedness
and the finite Cartan property. Induction numbers the remaining vertices
by one of the nine standard families.

The unique neighbor of the deleted vertex supplies the attachment index
and the two ordered entries. The previous leaf-extension classification
then gives an exact numbering of the enlarged standard matrix. The proof
composes this numbering with the equivalence that appends the deleted
vertex to the numbered remaining subtype. Every ordered integral entry is
retained.

The proof uses the explicit nonnegative-column inequalities and matrix
numberings in the supporting modules; it does not invoke a root-system
classification or a downstream group-theoretic theorem. It is an internal
proof of `Langlands.LinearAlgebra.FiniteCartanClassificationStatement` and
does not itself construct the actual-group bridge.
