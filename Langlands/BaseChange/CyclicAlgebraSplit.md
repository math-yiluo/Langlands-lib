# Cyclic coordinates over an algebraic closure

The residue field in `CyclicAlgebraStructure.exists_coordinates` is itself a
cyclic field extension. Its Galois property gives separability in every
characteristic. Formal étaleness of the field and of its finite product then
gives `IsCyclicAlgebra.formallyEtale_of_cyclic`.

Over an algebraically closed field the residue field of the coordinate
decomposition equals the base field, since it is a finite field extension.
The wraparound automorphism is therefore trivial and the number of coordinates
equals the cyclic degree. The identities for the residue coordinates show that
the original automorphism shifts them by one, including at the final index.
`IsCyclicAlgebra.exists_splitCoordinates_baseChange` applies the scalar-extension
theorem before taking these coordinates.

These algebraic lemmas supply the cyclic coordinates for the norm
differential and twisted determinant in Henniart–Lemaire, *Changement de base et
induction automorphe pour GLₙ en caractéristique non nulle*, §II.2.10, printed
pp. 70–71. The source identifier is
`provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`
and the retained PDF SHA-256 is
`7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`.
