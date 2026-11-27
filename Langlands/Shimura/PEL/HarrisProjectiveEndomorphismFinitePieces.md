# Finite pieces for a fixed graph polynomial

For a `ProjectiveEndomorphismGraphPieces` presentation,
`comparisonAllTests` extends the affine graph-labelled comparison
to the relative endomorphism functor on the full slice.
The universal relative homomorphism obtained from the affine comparison
defines an endomorphism of the representing scheme through the full
comparison. Its postcomposition maps are bijective on affine tests,
so `Picard.LineHom.isIso_of_bijective_affine` makes it an isomorphism.
Composing with its inverse produces the full comparison with the
prescribed affine values. `comparisonAllTests_affine` expresses
that equality.

`fibreGraphSectionRank` records the section dimension used by the
polynomial pieces on an affine test. For an algebraically closed
field test, `range_subset_open_iff_self` tests the piece by the
eventual section dimension over that field. The open cover places
the single point in some polynomial piece. Equality of eventual
evaluations identifies its polynomial with the prescribed one.

Over a noetherian affine base, `open_isFinite` gives finiteness of
each polynomial open over the base. The Néron homomorphism extension
gives the discrete valuation lifting condition on that piece because
its image is closed in the full endomorphism scheme.
Quasi-compactness, local finite type and separatedness then make the
piece proper. Formal unramifiedness makes it locally quasi-finite,
so the structure map is finite.
