# Local dynamic Borel data from a prescribed residue cocharacter

Worker 608, using the local-presentation construction of Worker 598,
the parabolic source geometry of Worker 606, and Worker 653's negative Borel
adapter.

This internal construction starts with a split maximal torus in a reductive
group scheme, a relative Borel containing it, a base point and a cocharacter of
the given torus. It explicitly assumes that on the residue fibre this
cocharacter presents the given Borel and has the given torus as its entire
centralizer. It does not construct that cocharacter or discharge those two
residue equalities.

`BorelDynamicNeighbourhoodData` retains an actual open immersion to the original
base whose image contains the specified point, a cocharacter of the actual
pullback torus, the positive Borel presentation, the centralizer equality, and
an actual closed negative relative Borel representing the opposite dynamic
parabolic.

The proof factors the cocharacter through the supplied Borel using the
all-test torus containment. Relative parabolic geometry gives smoothness,
affineness and geometrically connected fibres of the Borel. The prescribed
positive presentation persists on an open neighbourhood by
`Dynamic.exists_local_presentation_of_fieldPoint`. Independently,
`exists_open_centralizer_eq_range` spreads the residue centralizer equality.
Their fibre product is a common open neighbourhood. The original residue-field
point lifts to this fibre product, so its image contains the original point.
Both equalities pull back to that common neighbourhood; canonical pullback
comparisons and global dynamic representatives identify their iterated and
direct forms. The negative Borel adapter then supplies the final data.

The explicit witness in the existence proof uses the base change of the
supplied cocharacter. `borelDynamicNeighbourhoodOfResidue` chooses neighbourhood
data satisfying the recorded fields. Its output type does not record an
equality between its cocharacter and the base change of the supplied one, so
the public construction guarantees only those fields. The base scheme is
arbitrary and the construction is universe polymorphic. All nonpublic helper
sources remain private development dependencies pending their independent
acceptance and publication.
