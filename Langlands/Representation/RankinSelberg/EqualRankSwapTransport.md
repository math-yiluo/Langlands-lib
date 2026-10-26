# Algebra for equal-rank exchange

This supporting module for direct fixed-character transport
in JPSS equal-rank exchange isolates the diagonal at `-1`, its commutation
with the long Weyl representative, the trivial determinant weight and quotient
modulus, and the involutive scalar action of the actual central matrix `-I` on
a nonzero coefficient model.

The implemented matrix proofs use the actual diagonal entries and the
entry formulas for the long Weyl permutation. The identity is
`d * w = (-I)^n * (w * d)`. The determinant weight and quotient modulus
simplify at `-1` for every real absolute value. The scalar power law follows
by induction on the number of applications of `-I`; applying it twice to a
nonzero coefficient and cancelling proves that the scalar squares to one.

These are derived algebraic consequences of the published matrix and model
definitions. They do not assert a functional equation, factor existence, or
identification with a contragredient. Their provenance is internal supporting
algebra for the direct transport route, rather than a separately quoted
literature theorem. The intended consumer is the proof of
`EqualRankFactorSwapStatement`, via the coefficient-model and integral
transport modules.
