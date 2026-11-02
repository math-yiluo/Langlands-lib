# A scheme representing the full arrows of a Picard atlas

This is an internal representation construction from the actual point-fibre
presentation hypothesis. It uses the full arrow presheaf, the iterated-slice
equivalence, and the categorical total-presheaf representation construction.

Given a scheme `P` representing the point fibre of `L` against itself over
`U.left`, `atlasArrowRepresentation` first turns the lifted Yoneda isomorphism
into representation data and removes the universe lift. It transports the
data along the equivalence between schemes over `U.left` and the iterated
slice over `U`. The total presheaf is then represented by the underlying
object in `Over S`. Restoring the universe lift gives `atlasArrowSchemeIso`,
an isomorphism of the entire presheaves on all schemes over `S`.

`atlasArrowSchemeIso_snd` proves that the second endpoint corresponds to the
original map `P → U.left`. Consequently `exists_atlasArrowScheme_snd` uses
the smooth surjective point-fibre presentation evaluated at `U,L` to produce
an actual arrow scheme whose second endpoint is smooth and surjective. No
assumption about existence of global representatives for sheaf sections is
made. The first endpoint and the subsequent automorphism and quotient
constructions remain separate obligations.
