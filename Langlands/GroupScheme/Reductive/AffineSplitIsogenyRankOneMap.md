# Coroot maps and powered rank-one laws

This internal supporting construction uses the prescribed torus and root
maps to transport actual rank-one laws. The source and target coordinate
pairings are assumed to be the standard integer dot products. A fibrewise
root datum gives these pairing identities whenever a field algebra over
the base is supplied.

`corootMap` is the source exponent cocharacter followed by the actual torus
map. The transpose equation of the root-datum isogeny identifies the
composite of any exponent cocharacter with the exponent cocharacter
specified by the coweight map. The proof checks every target projection,
uses the published character/cocharacter pairing formula, and then applies
the standard pairing assumptions. The coroot equation therefore identifies
`corootMap` with the target coroot multiplied by its root factor. On every
scheme test the corresponding coroot point is the target coroot point
evaluated at that power of the original unit.

Additivity of a root-factor power shows that it fixes minus one, both as a
function and as a unit, including in characteristic two. Reflection
compatibility identifies the opposite powered root map and proves that its
exponent equals the exponent of the positive root.

`rankOneLaws_poweredRootFamily` transfers all four supplied actual target
rank-one laws to the powered pair, relative to the prescribed source torus
map and the source coroot. The two conjugation laws use equality of the Weyl
products and the formula for opposite powered roots. The square law uses
the coroot-point identity and the value of the power at minus one. For the
unit-denominator relation, a unit `d = 1 + x*y` has powered value
`d^q = 1 + x^q*y^q` by additivity and multiplication of powers. Applying the
target relation at these values and using the coroot-point identity proves
the asserted source relation.

The coefficient ring is arbitrary. Target rank-one laws and the two pairing
identities are explicit premises; no target powered map is assumed to be
an immersion. The module does not construct normalized data or prove
compatibility between distinct roots or the final isogeny theorem.
