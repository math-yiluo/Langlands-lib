# Determinant units of finite product bases

This internal algebraic prerequisite computes actual finite basis transitions
on a product of two modules over an arbitrary commutative ring `R`.

`productBasis a b` is the usual product basis, reindexed from
`Fin n ⊕ Fin m` to the standard `Fin (n + m)` using `finSumFinEquiv`.
`productBasis_toMatrix` identifies its transition matrix with the two
original transition matrices on the diagonal and zero off the diagonal,
up to simultaneous standard reindexing. The product basis coordinate
formulas prove this entry by entry. Simultaneous determinant reindexing and
the block triangular determinant formula give
`det_productBasis_toMatrix`.

`unit_productBasis` proves multiplicativity of the existing mixed determinant
transition unit even when the two presentations of each summand use
different finite rank indices. Equal ranks reduce to the preceding matrix
formula. A basis rank inequality forces the coefficient ring to be trivial;
its units are then a subsingleton, which proves the remaining branches.
No nontrivial-ring or positive-rank assumption is imposed.

`unit_map` states that applying the same actual linear equivalence to both
bases preserves the mixed determinant unit. It follows from the existing
ring-map compatibility theorem with the identity coefficient homomorphism
and the basis-map coordinate formulas. This transports the product formula
to actual section bases of a sheaf biproduct. The provenance is internal:
standard product bases, existing mixed units and elementary matrix
determinant identities supply the whole proof.
