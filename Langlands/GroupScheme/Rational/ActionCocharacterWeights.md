# Intrinsic action weights under cocharacter restriction

This internal supporting module works over an arbitrary field `k : Type u`,
with an affine group scheme `G` and an actual automorphic action `b` of a
commutative group scheme `S`. It transfers the published split-torus Lie
decomposition to restrictions of the acting torus.

`actionWeightSpace_le_restrict` restricts each intrinsic weight along a
homomorphism `f : T ⟶ S`. It needs no splitness or finite type assumption.
The proof uses the all-test differential weight equation and the formula
for evaluating a composite character. `actionWeightSpaceRestrictMap` bundles
this containment as the canonical linear inclusion; its underlying vector
is unchanged.

For `G` locally of finite type and both acting groups split tori,
`actionWeightSpace_restrict_eq_iSup` identifies a weight of the restricted
action with the sum of all original weights having that restriction.
The sums of these grouped original spaces span the full Lie algebra.
Each grouped sum lies in its corresponding restricted weight space, and
independence of the restricted weight decomposition forces equality.

`actionWeightSpace_cocharacter_eq_iSup` specializes to a cocharacter and
uses the actual character/cocharacter pairing to index a power of the
multiplicative group. `semigroupWeightSpan_positive_eq_restrict` then
identifies the span selected by the strictly positive pairing halfspace
with the sum of all strictly positive weights of the restricted action.
It allows zero weights and does not assume the cocharacter is generic.

`cyclicTail_le_positiveSemigroup` records that every positive multiple
of a character with positive pairing is in that halfspace, for every
cyclic-tail index.

The provenance is internal, from the actual differential action weights,
split-torus decomposition, the character pairing, and the existing
conjugation-only cocharacter weight formulas. No subgroup containment,
representability, or cyclic-root comparison is asserted here.
