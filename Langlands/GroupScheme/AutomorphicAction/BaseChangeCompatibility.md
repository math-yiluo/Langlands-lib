# Restriction and conjugation compatibility of pulled-back actions

This internal construction works over arbitrary schemes in a common universe.
It reuses `AutomorphicAction.baseChange` from `AutomorphicAction/BaseChange`,
whose action morphism is obtained from the original action at the universal
pair using the published pullback point equivalence. This is the same
universal-pair morphism as the direct construction of the reviewed contribution.
The existing `baseChangePointsEquiv_act` identifies its value on every relative
test scheme with the original action over the old base.

The published `ext_act` from `Dynamic/ActionConjugation` tests equality of
actions at the universal pair to recover equality of their morphisms. With
this criterion, the all-test pullback formula proves `baseChange_restrict`
and `baseChange_conjugation`: pullback commutes with restriction along every
group-scheme homomorphism, and the pullback of conjugation along a homomorphism
is conjugation along its pullback. These statements require no affineness or
smoothness hypothesis.

This construction does not assert a comparison of Lie modules or determinants.
