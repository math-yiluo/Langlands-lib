# Equivariance of actual exact-weight quotient maps

This internal adapter for Task 7200 proves actual equivariance of each
exact-weight quotient map under a supplied realizing cocharacter. The
commutative base ring and universe are arbitrary. No field, reducedness,
connectedness, nonempty-base or positive-rank hypothesis is imposed.

The inputs are the existing `RootHeightChart C`, `RootWeightData W`, a
monomorphic ambient homomorphism `j`, an actual split-torus homomorphism `t`,
and torus-equivariant root parametrizations whose ambient maps are precisely
the chart roots. These are the inputs of `RootWeightTorusAction`. The module
constructs no root chart or realizing cocharacter.

`W.cocharacterAction j hroot hu v d` restricts the actual `W.torusAction`
on `W.groupScheme d` along the actual
`splitTorus.exponentCocharacter v`. Thus it is a morphism defining a genuine
automorphic action, with the actual induced group law on the represented
term. It does not replace that group by the additive group of its underlying
coordinate affine space.

`torusChar_exponentCocharacter` uses the existing actual
exponent-character/cocharacter composition identity to identify a root
character restricted to `v` with the integer power character given by their
pairing. This identity holds on every scheme test.

`quotientMap_isEquivariant_of_pairing` assumes that the pairing of each root
in `W.exactSupport d` with `v` equals one integer `N`. It proves that the
actual group homomorphism `W.quotientMap d` is equivariant from the preceding
cocharacter action to the existing vector-group scalar action
`VectorGroup.weightAction (Gm.powerHom N)`. The proof evaluates both maps
at an arbitrary acting point and term point over an arbitrary test scheme,
then checks each exact-weight output coordinate. The source action scales
that coordinate by its original root character; restriction replaces this
factor by the common power character. The existing
`coordinates_torusAction_inclusion` and `quotientPoints_coord` equations
give the same projected coordinate on both sides.

`quotientMap_isEquivariant_of_realization` specializes to a natural multiplier
`q` and pairings `coPairing (ch (index k)) v = q * W.weight k` for all original
chart roots. At term `d` the common natural exponent is `q * (d + 1)`.
The target action is definitionally the `VectorGroup.powerWeightAction`
used by `LinearQuotientComparison`. `realization_quotient_power_pos` proves
strict positivity of that exponent for `0 < q`, for every `d`. No coordinate
is selected in the empty-layer case, so rank zero is included.

The provenance is internal: the result projects the actual diagonal
torus-action equation through the existing exact-weight quotient map and
uses actual exponent-character composition. It uses no root structural
existence theorem and no field-only weight comparison. Existence of the
charts and realizing cocharacters, comparison of different tori, and the
global filtration descent and assembly remain separate obligations.
