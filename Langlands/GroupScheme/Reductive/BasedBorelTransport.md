# Actual transport of canonical based dynamic Borels

This internal construction joins the published `BasedAffineBorel` and
`Torus.ExponentTransport` interfaces. It works over an arbitrary scheme and on
every relative scheme test, including nonreduced tests.

`BasedBorelTransport.cocharacter` realizes the sum of positive coroots of a
finite based root datum as an actual cocharacter through a supplied coordinate
torus inclusion. The root datum uses the integer coordinate lattice in both
arguments.

`BasedCoordinateIso` records supplied actual ambient and coordinate-torus
isomorphisms, their inclusion square, a based root-datum equivalence and its
all-test character pullback formula. Both lattice pairings are explicitly
required to be the standard integer dot products. The equivalence goes from the
target root datum to the source root datum: its weight map is character
pullback, and its contravariant coweight map carries source exponents to target
exponents. The structure does not assert that these isomorphisms exist or lift
any given root-datum equivalence.

`torus_cocharacter_comp` first identifies the integer transpose of the supplied
character map with the equivalence's coweight map. The published reindexing of
the positive-coroot sum then identifies the transported exponent exactly.
`cocharacter_comp` uses the inclusion square to give equality of actual ambient
cocharacters; `cocharacter_inv_comp` is its inverse form.

`parabolic_comap` applies the published functoriality of dynamic parabolics to
this equality. Thus the comparison uses actual cocharacters and all-test
functors, with no passage from geometric-point equality to subgroup equality.
`range_torus_comp` also records the torus range equality from the supplied
square.

For any two supplied actual representatives of these dynamic parabolics,
`parabolicIso` constructs an actual source isomorphism. The theorem
`parabolicIso_hom_comp` states its exact inclusion equation.
`range_parabolic_comp` and `range_baseChange_parabolic_comp` give equality of
the actual inclusion ranges before and after arbitrary base change. These
equalities can be used by the existing invariant closed-subgroup descent
constructor.

There is no affineness, reductivity or reduced-root-datum hypothesis in this
transport construction. It does not prove the representatives are Borels:
that assertion, for the affine canonical construction, is supplied separately
by `AffineRegularBorel.isRelativeBorel_positiveCorootSum` from its full
fibrewise root-datum, reductivity and maximal-torus hypotheses. Pullbacks of
those affine representatives may be used here because dynamic representability
is preserved by base change. No cocycle, effective object descent, pinning
isomorphism existence or inner-form existence is supplied by this module.
