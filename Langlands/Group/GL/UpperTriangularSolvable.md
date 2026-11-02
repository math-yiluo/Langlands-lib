# Solvability of the upper triangular matrix group

This helper develops the actual `upperTriangularSubgroup n R` over an arbitrary
commutative ring. It is internal infrastructure for the GL_n Borel proof.
Milne, *Algebraic Groups* (2017), Example 17.7, printed p.354 (PDF p.370),
identifies the upper triangular subgroups as the Borel subgroups. Solvability
is one of the ingredients of that example. The commutative-ring formulation
here is a derived strengthening of the field point-group ingredient.

The proof inducts on matrix size. The homomorphism `leadingWithDiagonal`
records the leading principal block and the final diagonal unit. Its kernel
has only the final column above the diagonal as free entries. Multiplication
adds those entries, so the kernel is abelian. The quotient maps into the
product of the smaller triangular group and the commutative unit group.
Mathlib's extension criterion for solvability finishes the induction,
including size zero. No group-scheme smoothness or maximality is claimed.
