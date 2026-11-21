# Finite-order lifts of the embedded unramified residue units

`ResidueCyclicLift` records an integral element whose residue has order the
size of the residue unit group and whose corresponding integral power is
one. In a Henselian local ring with finite residue field, `chooseLift`
first chooses a generator of the residue units. If their order is `m`, this
is a simple root of `X^m - 1`. The derivative is nonzero because `m` is
prime to the residue characteristic and the residue generator is nonzero.
Henselian lifting produces the specified actual element of the local ring.

`subfieldResidue_card` identifies the residue cardinality of the actual
unramified integer subfield with `q^d`, where `q` is the base residue
cardinality and `d` is the reduced division degree. The proof uses the
published residue degree equality and the size of a finite vector space.
`subfieldResidueCyclicLift` applies the lift to this actual integer ring.

This is derived arithmetic for the distinct tangent characters of the
maximal unramified subring in Drinfeld 1976, §2A, printed p. 109. The
lift supplies the integral finite-order element used to test those
characters in the special-kernel rank argument.
