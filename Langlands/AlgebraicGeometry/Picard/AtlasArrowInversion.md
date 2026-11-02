# Inverting actual Picard arrows

This internal construction uses the full arrows of an actual Picard family.
The auxiliary `pullIso_symm` proves inversion compatibility for any
category-valued pseudofunctor; `totalArrowInverse` constructs the corresponding
inversion on its total point-fibre presheaf. The Picard specialization
`atlasArrowInverse` exchanges the two test morphisms to the family and
inverts the retained pullback isomorphism. Its naturality follows because
coherent pullback of an inverse is the inverse of coherent pullback: the
pseudofunctor composition comparisons appear in reverse order. Inversion
is an involution and thus defines `atlasArrowInverseIso`. It exchanges the
first and second endpoint natural transformations on all tests.

`exists_atlasArrowScheme` starts from the represented full arrow scheme
whose second endpoint is smooth and surjective. The Yoneda fully faithful
functor carries inversion to an isomorphism of the arrow scheme. The first
endpoint is the composite of that isomorphism and the second endpoint, so
it too is smooth and surjective. The conclusion retains the full presheaf
isomorphism and the equalities of both endpoint transformations. No
quotient or representation of Picard classes is inferred by this lemma.
