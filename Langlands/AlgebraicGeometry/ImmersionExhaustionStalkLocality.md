# Spreading fullness from base stalks

`IsomorphismLocalization.OpenSpreadingStatement` concerns a morphism between
two finitely presented schemes over a scheme \(S\). Finite presentation is
expressed by local finite presentation, quasi-compactness, and
quasi-separatedness of both structure maps. If the morphism is an isomorphism
after base change to \(\operatorname{Spec}\mathcal O_{S,s}\), it is an
isomorphism after base change along an open immersion whose image contains
\(s\).

The proof chooses an affine neighborhood of \(s\). The germ map on that
neighborhood identifies the stalk as a prime localization and gives the
canonical stalk map after composing with the chart inclusion. The
localization-spreading theorem produces a principal localization away from
an element outside the prime. Its spectrum is an open subscheme of the
chart containing \(s\). The compatibility of iterated and composite slice
pullbacks gives the isomorphism over this neighborhood.

`ImmersionExhaustion.Family.full_of_stalk_full` applies this result to a
nonempty directed increasing family of immersions over a noetherian base.
The ambient structure map is locally of finite type and quasi-compact.
These hypotheses make the ambient scheme noetherian. Each member has
noetherian underlying space by the immersion, and its structure map is
locally of finite type. Both structure maps are then finitely presented.
For each ambient point, a member that is full over its image's base stalk
spreads to a base neighborhood. The pullback of that neighborhood is an
open neighborhood of the ambient point, and the inclusion remains an
isomorphism there. The finite-open-cover fullness theorem chooses one
global index.

This is an internal implementation of the spreading step in SGA 3, Exposé
IX, Lemma 6.2 and footnote 41, printed pp. 53–54 (retained PDF pp. 23–24).
The registered source is `sga3-expose-ix-gille-polo-2009`, SHA256
`7c1e3d5b9d01ad01d0dd7b8b62045d012052e7890fb37adc3e7934ebb5fd6fc3`.
