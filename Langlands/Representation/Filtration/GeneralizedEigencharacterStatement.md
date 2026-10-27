# Generalized eigencharacters detected by actual graded quotients

Author: Worker 573.

`Langlands.GeneralizedEigencharacterFiltrationStatement` is a closed
proposition about a supplied actual `RepFunctorFiltration F n`. At each
object `X`, this is a finite increasing chain of invariant submodules that
starts at zero and ends at the whole representation `F.obj X`. Its graded
objects are the published actual successive quotients, with repeated steps
and zero graded pieces allowed.

Let `R` be any commutative ring, `G` and `H` any monoids, and
`ι : H →* G` any homomorphism. Restrict the ambient and graded actions along
`ι`. For any character `χ : H →* Rˣ` and natural number `k`, if the ambient
`characterSpace` is nonzero, then the `characterSpace` in some graded
quotient is nonzero for the same `χ` and the same `k`. The character space
consists of vectors killed by the `k`th power of every operator
`ρ(ι(h)) - χ(h)`, with a single power for all `h`. In particular, a
generalized eigencharacter of the restricted ambient representation occurs
in some restricted graded piece.

The ring, both monoids, representation carrier and source category have
independent universes, including the category's morphism universe. No
topology, character-kernel openness, commutativity of the monoids,
injectivity of `ι`, admissibility, irreducibility, finite dimension or
simple graded factors is assumed. A length-zero filtration is covered;
its ambient representation is zero, so the nonzero-space premise cannot
hold.

This is an internal linear-algebra consequence of the published uniform
`characterSpace` and actual filtration constructions, not a transcription
of a literature theorem. The intended deduction takes a nonzero vector in
the character space and a pair of consecutive steps for which it lies in
the upper step and outside the lower step. The vector's class in their
quotient is nonzero. Restriction to the invariant upper step and the
equivariant quotient projection preserve all the character-defect
equations with exactly the same power. This module states the implication;
it supplies no proof.

For the geometric-lemma application, construction of the actual filtration,
identification of its graded pieces, refined-induction central-spectrum
comparison, extension of restricted characters, and chamber or modulus
comparisons remain separate obligations. This statement asserts no
geometric lemma, Jacquet bound or analytic temperedness result.
