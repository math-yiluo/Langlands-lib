# Finite product covers and the literal ambient intersection

This internal construction removes the union-equality input from finite
intersection recognition when the local pieces come from every pair of
members of two finite full-domain covers of the unchanged input algebras.
It uses only the actual cover and extension constructions; it asserts no new
literature result.

`iUnion_extend_finiteCover` proves that the extensions of a finite cover of
`U.algebra` have union exactly `U.locus`. Each extension includes in `U`.
Conversely, the range equation for `U.ambientMap` lifts an ambient point to the
spectrum of `U.algebra`, where the given cover supplies a member containing it.
The extension image formula places the original ambient point in that member.

`iUnion_extend_inter_finiteCover` indexes all pairs of cover members by an
explicit finite equivalence. A point of the union lies in both input loci by
the two extension inclusions. A point of the input intersection lies in one
member of each extended cover by the first lemma; the inverse equivalence
gives the required paired index. The proof applies equally to empty covers and
does not assume the spectra are nonempty.

`FiniteIntersectionData.ofFiniteExtendedProductCover` takes those two covers,
a finite whole-spectrum cover of a candidate algebra, the index equivalence,
actual local intersection pieces, their two inclusion arrows, bounded local
equivalences and exact equations for the original algebra legs. The piece
loci and the candidate-cover loci must be the literal intersections and
product pullbacks. The constructor derives the union equality using the two
lemmas and passes the data to `ofExtendedProductCover`, which derives
saturation from the finite local comparisons.

Thus the candidate algebra, its maps, the cover and bounded comparisons are
retained. The global ideal and the existence of the local comparisons remain
separate obligations, including ideal-descent effectiveness in the closed
quotient application. This is not a proof of `SpecialSetIntersectionStatement`.
Independent coefficient, ambient and original-index universes are retained,
with no strictness, reducedness, nontrivial-valuation or global Hausdorff
assumption.
