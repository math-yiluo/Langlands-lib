# Irreducible subrepresentations carrying an actual Jacquet exponent

Worker 148. This internal construction selects an irreducible smooth
subrepresentation carrying a supplied generalized central character of an
admissible Artinian representation. It specializes to the normalized
Jacquet module of an arbitrary represented rational parabolic, on the
original actual Levi points.

`Classification.scalarCharacterSubrepresentation` is the subspace where
every element of the supplied commutative group acts by its prescribed
ordinary scalar. Centrality makes it invariant under the whole ambient
group. A nonzero generalized-character vector is fixed by an open
subgroup. Admissibility makes its fixed-vector space finite dimensional,
and centrality makes that space stable under the commutative action.
The published generalized-to-ordinary eigenvector theorem gives a
nonzero vector in the ordinary scalar subrepresentation.

Artinianity of the group-algebra module makes its subrepresentation
lattice atomic. Choosing an atom below this nonzero ordinary character
space gives a simple actual subrepresentation. The canonical smooth
inclusion is injective, and membership in the ordinary character space
gives the exact scalar action on every vector. The chosen smooth
representation uses the same carrier universe as the original one.
No admissibility or finite-dimensionality of the whole carrier is
substituted for Artinianity.

For `exists_irreducible_leviJacquet_subrepresentation_of_exponent`, the
source representation is admissible, and finite length of its specified
actual Levi Jacquet module is an explicit additional premise. Published
unconditional Jacquet admissibility is transported through the canonical
Levi-point equivalence. The original normalized Jacquet exponent is a
generalized eigencharacter for the identical action after this transport.
The actual component is central in the actual Levi, so the general
selection theorem applies. Finite length supplies its Artinian premise.
The resulting object, inclusion and scalar character are all on the
actual Levi, with independent field and representation universes.
`irreducibleLeviJacquetExponentSubrepresentation` chooses this object
together with its irreducibility, injective inclusion and scalar certificate.

The provenance is internal, combining ordinary eigenvector extraction,
Artinian atom selection, smooth subrepresentation construction, and the
published actual Jacquet and Levi transport APIs. This does not prove
preservation of Jacquet finite length, construct an induction quotient,
prove temperedness of an untwist, or establish Langlands exhaustion or
the classification.
