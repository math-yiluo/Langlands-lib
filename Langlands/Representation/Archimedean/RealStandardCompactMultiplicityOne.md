# Compact coefficient multiplicity one for real standard modules

This internal argument specializes the sign and mode equations to the real
standard module. It uses the rotation and sign formulas for `compactMatrix`.
The required sign covariance follows from the independent pair interchanges
and the diagonal gains. Conversely, every qualifying linear form is
invariant under all pair interchanges and obeys the individual pair and
singleton sign equations. The proof realizes these generators with the
diagonal units `signParameters`.

The Fourier windows agree because the threshold for an induction block is its
absolute weight plus one. The singleton exponents are the corresponding
position signs, each zero or one. With the rows ordered by their positions,
`RealCompactFunctional.exists_functional` supplies a nonzero functional
and proves uniqueness up to scalar under these constraints.

The compact coefficients are continuous because each entry of a compound
matrix is a finite product of determinants, and the linear forms act on a
finite-dimensional space. `RealCompactWitnessExtension` extends these
coefficients into the standard module. Evaluation at the identity recovers
the linear form. The result `realStandardExistsCompactScalarVector` gives
a nonzero vector scaled by every compact-equivariant endomorphism.
