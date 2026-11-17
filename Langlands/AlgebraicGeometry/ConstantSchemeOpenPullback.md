# Restricting constant schemes to connected open refinements

This is an internal consequence of the coproduct and open-immersion APIs. For
schemes `V` and `U` in universe `u`, an open immersion `i : V ⟶ U`, and an index
type `I : Type u`, the pullback to `V` of the coproduct of copies of `U` over
`U` is isomorphic over `V` to the coproduct of copies of `V`.

The proof first shows that the coproduct map induced by `i` is an open immersion,
using the published theorem that a Zariski-local property of target morphisms
passes to coproduct maps. The coproduct square commutes. On underlying points,
the homeomorphism from the disjoint union shows that the inverse image of the
range of `i` is the range of this coproduct map: a point in the summand indexed
by `j` lies in that inverse image exactly when its coordinate is in the range
of `i`. The open-immersion pullback criterion therefore proves the square is a
pullback. Its canonical pullback isomorphism gives
`constantSchemeOpenPullbackIso` in the slice category over `V`.

`restrictConstantTrivialization` composes the pullback-composition isomorphism,
the pullback of a supplied trivialization of a relative scheme `C` over a base
`S`, and the constant-scheme pullback isomorphism. It keeps the original index
type and works for every open immersion into the trivializing cover.

`connectedEtaleRefinementTrivialization` applies this construction to the chosen
connected open refinement of an étale surjection onto a Noetherian local
spectrum. The imported refinement module provides connectedness of that open
subscheme and étaleness and surjectivity of its map to the base. This module
requires a supplied trivialization and proves no unconditional local-constancy
or outer-isomorphism representability assertion.
