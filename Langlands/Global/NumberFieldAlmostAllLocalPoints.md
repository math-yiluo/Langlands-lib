# Local points of smooth geometrically connected number-field schemes

This internal construction is derived from the published arithmetic model
existence, geometric connectedness descent, and uniform Lang–Weil results.
It is intended for the torsor clause of Conrad's Exercise 5.5.3(iii).

`exists_numberFieldSmoothConnectedModel` starts with a separated finite-type
model supplied by `numberFieldSpreadSeparatedExistence`. It applies
`numberFieldSpreadEventualSmoothGeometricallyConnected` to the map to the
terminal scheme over the same integer base. This enlarges the finite set of
places until the structure map is smooth and geometrically connected.
Finally, it enlarges to a principal integer level, which is of finite type
over the integers. Two pullback-composition isomorphisms retain the original
generic fibre.

`eventually_nonempty_ringPoint_of_smooth_geometricallyConnected` applies
`numberFieldComponentAlmostAllIntegralPointLifts` with the proved
`uniformLangWeil`, to the model's structure morphism. The base of this morphism
is the terminal scheme over its ring of S-integers, so it has a canonical
point over every completed integer ring away from S. The lifting theorem
excludes one further finite set of places. Outside the union, its integral
point maps to a completion point of the original scheme using change of
coefficient ring, the pullback adjunction, and the specified generic-fibre
isomorphism. The result requires no common dimension for all model fibres.
