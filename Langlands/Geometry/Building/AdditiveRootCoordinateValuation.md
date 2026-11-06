# Additive root coordinates and normalized root values

This internal adapter transfers an additive field valuation along a supplied
multiplicative equivalence from the additive coordinate group of a field to
one actual rational relative root group `rootGroupPoints i a`. It uses the
existing root group, with no replacement subgroup. The base field and the
coordinate field have independent universes.

`additiveRootValue` is the coordinate value on this subgroup and infinity
everywhere else in the rational ambient group. The coordinate formula is
exact. On the root group, the infinite value occurs precisely at the
identity. Multiplication has value at least the minimum of the two input
values, and inversion preserves value. These facts define an actual
subgroup of ambient rational points at every real threshold. They are the
local V1 properties for this one root.

If conjugation by an ambient point is multiplication by a scalar in the
coordinates, the field valuation multiplication law gives the precise
additive shift. This lemma retains its coordinate-conjugation hypothesis;
it does not construct a scalar description of an arbitrary normalizer or
centralizer point.

`henselianAdditiveRootValue` specializes the construction to the normalized
valuation on a separable coordinate field, using
`HenselianSeparableIntegerAddValuation`. The integer order of a nonzero
embedded base scalar agrees exactly with `IntegerValuation.order`.
Surjectivity of the original integer valuation gives every integer as a
value on the actual root group. Injectivity of the integer-to-extended-real
map makes the root-value image infinite; its extended cardinality therefore
exceeds the V0 lower bound of three.

The provenance is the direct transport of field valuation laws and the
previous separable-extension construction. The intended application is the
R1 branch of Kaletha–Prasad Construction 6.1.17. This file does not assert
that an actual additive root-coordinate equivalence exists for arbitrary
quasi-split groups. It also supplies no global root family, reflection,
commutator, opposite-factor or doubled-root identities, and no apartment or
full centralizer compatibility. Those remain separate proof obligations.
