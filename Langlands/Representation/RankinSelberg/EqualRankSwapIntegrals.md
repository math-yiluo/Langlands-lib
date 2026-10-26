# Equal-rank integral exchange at a fixed character

This supporting module uses the actual quotient translation by the minus-one
diagonal. For two model vectors, translate both and exchange them. Their
original equal-rank integral is unchanged: multiplication of the coefficient
values commutes, the diagonal fixes the last row, and both its determinant
weight and the quotient measure modulus are one. Consequently the original
rational-continuation value sets coincide, without assuming any analytic
existence result.

The module also transports each original continuation unchanged and each
dual continuation by the stated constant. The constant is nonzero because
both model scalars are units. In the reverse direction, multiply a target
continuation by its reciprocal after choosing preimages of the two model
vectors. The two dual value sets therefore have the same Laurent span and
the same normalized-generator relation.

For the dual integral, commute the diagonal past the long Weyl matrix. Each
coefficient contributes the `n`-th power of its supplied minus-one scalar;
the dual integral gains their product. The Schwartz--Bruhat test is retained.
The measure law is an explicit hypothesis and will be discharged for every
compatible quotient measure by the published character-change measure theorem.
All integral identities concern total Bochner integrals, so the proof does not
insert an integrability assumption.

These internal derived lemmas support the direct JPSS exchange route.
`EqualRankSwapEquations` uses them to transport the defining functional
equations. No inverse Fourier or contragredient identification is asserted.
