# Conjugation and recentering of the source orbit measure

Waldspurger (2003), III.7 and VI.3, integrates over the actual unitary
unramified twist orbit with the measure for which the twisting map
locally preserves the I.1 character Haar. This module supplies its
conjugation and base-change comparisons.

`characterConjugation_map_stabilizer` uses injectivity of the literal
pullback on discrete-series classes and its equivariance for twisting
to identify the actual self-twist subgroups. `orbitConjugation` uses the
corresponding homeomorphism of their character quotients. Its value is
the pullback by inverse Levi conjugation. The orbit measure comparison
uses the fixed I.1 character Haar comparison and the equal reciprocal
self-twist factors on the two pushforwards.

`orbitConjugationRecentered` composes this transport with the identity
on classes into the orbit presented at the target's own base. Its
measure comparison uses Haar translation invariance through the
existing twist base-change theorem. The orbit equality gives the
unitary twist for recentering, and the value theorem specifies the
result on every class independently of that witness. Both displayed
split-valuation finite-index hypotheses enter through the original
source-normalized measures.
