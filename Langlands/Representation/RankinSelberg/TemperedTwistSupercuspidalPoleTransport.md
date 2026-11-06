# Removing the real twist from supercuspidal pole existence

Author: Worker 1743.

This is an internal reduction for
`Langlands.RankinSelberg.TemperedTwistSupercuspidalPoleStatement`.
It does not prove pole existence. It proves that the published target is
equivalent to its untwisted case, with the same independent field,
representation and partner universes.

`isPadicRankLPolynomial_realPowerTwist` says that opposite real determinant
twists of the two representations preserve the entire certified L-polynomial.
For positive ranks it specializes the published
`isPadicSymmetricLPolynomial_twist` from `RankOneTestReduction`, identifying the
inverse of the real-power character with its negative real power. The
arbitrary-rank relation is false if either rank is zero, so those cases are
reflexive equivalences. Both rank orders, and the existence and universality
of compatible quotient measures, are inherited from the published theorem.

`UntwistedTemperedSupercuspidalPoleStatement` states exactly the partner
existence conclusion for the original tempered representation, with no real
twist on it. It retains irreducibility, supercuspidality, both rank bounds,
the actual pair L-polynomial certificate and the root at one.

`temperedTwistSupercuspidalPole_of_untwisted` applies that assertion to obtain
a partner `ρ` and polynomial `P`. It replaces `ρ` by `ν^(-u)ρ`. Smoothness is
part of `segmentFactor`; the published determinant-twist theorems preserve
irreducibility and supercuspidality. Opposite-twist invariance supplies the
same polynomial for `(ν^u τ, ν^(-u)ρ)`. The rank bounds and root are unchanged.
The partner's carrier remains in its original universe.

`temperedTwistSupercuspidalPole_iff_untwisted` proves the converse by taking
`u = 0` and simplifying the real-power twist.

The provenance is internal: these are algebraic consequences of the published
determinant-twist invariance, real-power-character identities and
supercuspidality transport. The analytic pole-existence and classification
obligations described in the target's paired Markdown remain open premises.
No additional analytic assertion from the literature is used here.
