# Ordinary real equal-rank place tests

`realEqualOrdinaryPlaceTestsPositiveRank` proves
`RealEqualOrdinaryPlaceTestsPositiveRankStatement`. At a real place, for each
pair of supplied cuspidal realizations of `GL_(r+1)` with `0 < r`, it gives
two actual Whittaker restrictions for opposite characters, a Schwartz row
and a compatible quotient measure whose ordinary integral is nonzero at
points arbitrarily far to the right.

The normalized actual Whittaker intertwiner for the first realization
has a compact-finite coefficient with value one at the identity. For the
second realization, an actual coefficient for the inverse character has
nonzero value at the identity. The real uniform Whittaker model gives their
simple-root gauge estimates. If all the asserted equal-rank tests vanish on
right half-planes, `realEqualOrdinaryDescent` gives adjacent-rank vanishing
for every compact-finite value of the first intertwiner against the padded
restriction of the second coefficient.

`RealUnequalPositiveRank.descent_to_rankZero` iterates that vanishing down
to the integrals over `GL₁(ℝ)`. It applies to the normalized coefficient and
its first-root derivative, which is a value of the same intertwiner on a
compact-finite vector. The rank-one Mellin inversion criterion
`RealUnequalRankZero.value_eq_zero_of_integrals_eq_zero` then forces the
product of the two evaluations at the identity to be zero. Both factors
were chosen nonzero.

Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), Theorem 2.7(ii),
author-posted p. 10, obtains compact-finite equal-rank tests with Schwartz
rows in the stronger form of a generation result. The argument here uses
only ordinary nonvanishing for actual restrictions. The first descent uses
the equal-rank last-row coordinates of §14.2, pp. 105–107.
