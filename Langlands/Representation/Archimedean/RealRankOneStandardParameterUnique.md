# Real standard parameter uniqueness in ranks zero and one

`realRankAtMostOneStandardParameterUnique` proves
`RealRankAtMostOneStandardParameterUniqueStatement`. For total rank at most one,
an injective compact and Lie intertwiner between the actual real standard
modules identifies their block lists up to permutation.

The proof uses the Library's rank-zero and rank-one models. In rank zero both
lists are empty. In rank one both lists consist of a single real character.
Evaluation at the identity identifies each compact-finite module with the
complex line. The principal-series derivative formula of
`RealSubquotient.rightDerivative_upper_apply_one` makes the identity direction
in the Lie algebra act by the exponent. Evaluating the right translate by
the rank-one sign reflection gives the parity sign. On a nonzero image vector
of the intertwiner, each action gives equality of the two scalar values.
The two possible parity signs are distinct. Equal exponents and equal
parities determine the actual character and hence the block.

This is an internal consequence of the Library's concrete rank-one model.
It provides the two initial ranks of the real standard parameter comparison.
