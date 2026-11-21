# Composition on the original split special fibres

`splitQuasiIsogenyOnBaseChange` transports a split rational map from the
split of the two pulled-back primal towers to the pullbacks of the two
original split towers. This uses the actual rational split comparisons.
For an order-linear primal map it is the underlying isomorphism of
`splitOrderRigidifierOnBaseChange`.

`splitOrderRigidifierOnBaseChange_trans` computes composition of these
transported maps. The intermediate comparison cancels its inverse.
The primal maps compose and the multipliers multiply by the split
composition formula. In particular, the calculation applies on the
actual special fibres of a frame, a target, and a second target.

Harris (1997), Appendix, printed pp. 113–114 (PDF pp. 39–40), uses
precomposition of the special-fibre rigidifier in the frame action and
in (A.4). Rapoport–Zink (1996), §6.43, printed p. 309 (PDF p. 321),
gives the split presentation preceding (6.17).
