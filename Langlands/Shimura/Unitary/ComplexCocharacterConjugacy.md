# Inner conjugacy of actual Harris cocharacters

`ComplexCocharacterConjugate χ ψ` specializes the equivalence relation
`GroupScheme.HomConjugate` to actual morphisms from the complex multiplicative
group scheme to `D.complexRationalGroupScheme`. Its witness is a single complex
point of that group scheme and its assertion is equality after the scheme inner
automorphism. The arithmetic datum retains the number fields, central-simple
unitary algebra, and compatible scalar towers of the existing constructions.
The relation itself does not require a choice of signature charts.

The general helper `GroupScheme.affineCocharacterValue_comp_iso` compares two
ways to evaluate a cocharacter through a group-scheme isomorphism to a base
change. It follows from associativity of morphism composition under the existing
point equivalence. Specializing it gives `complexCocharacterValue_eq_points`:
evaluation in the rational affine model equals evaluation on the identity test
scheme followed by `complexRationalPointsEquiv`.

`complexCocharacterValue_inner` applies this equality to an inner automorphism.
The existing inner point formula and multiplicativity of the point comparison
give `g χ(u) g⁻¹` in rational-model coordinates, for every complex unit `u`.
Consequently, `finrank_complexCocharacterWeightSpace_of_conjugate` proves that
conjugate scheme cocharacters have the same inverse-weight rank at every CM
embedding. This uses the constructed weight-space conjugation equivalence, not
an assumed numerical invariance. This rank assertion retains the Harris charts
`C` and compatible CM section `hΦ` used to define the embedding weight spaces.

Finally, `complexCocharacterConjugate_diagonal_iff` specializes the relation to
the published diagonal cocharacters and their support-cardinality classification.
The equality tested is still equality of scheme morphisms. No converse from
weight-rank equality for arbitrary cocharacters is asserted here.

The provenance is internal: these definitions and comparisons connect the
published actual inner automorphisms, cocharacter evaluations, embedding weight
spaces, and diagonal classification. This module neither proves the Galois
stabilizer comparison nor defines or computes an additional reflex field. The
Galois comparison remains a separate mathematical obligation.
