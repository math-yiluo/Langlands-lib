# The unlinked character-induced swap

`realCharacterInducedSwap` has exactly the Library proposition
`Langlands.Archimedean.RealCharacterInducedSwapStatement` as its type. It adds no
hypotheses and retains arbitrary ambient rank and surrounding lists.

Put `ell = |d.weight| > 0`, `a = d.exponent + ell/2`, `b = d.exponent - ell/2`,
and `s = c.exponent`. The GL3 proof splits on whether `s-b` is an integer. If it
is not, neither `s-b` nor `s-a = s-b-ell` is an integer; hence neither is a
rank-one exceptional value. The two-factor generic Frobenius composite supplies
the injective exact intertwiner.

If `s-b = m` is integral, the original real-exponent order makes `m > 0`.
The unlinking hypothesis forces `m <= ell`: if `m > ell`, then
`s-d.exponent = ell/2 + (m-ell)` is precisely a forbidden linked parameter.
For `0 < m < ell`, the interlaced integral construction supplies the map.
For `m = ell`, parity splits the endpoint. When `ell + c.parity.val` is even,
the two factors have parameters `0` and `ell` and both are generic: positivity
rules out negative exceptional values, and parity rules out the positive ones.
When that sum is odd, the endpoint tail construction supplies an equivalence
and hence an injection.

`RealInjectiveIntertwinerExists.in_stages` transports this GL3 map through
arbitrary `pre` and `post`. The two exchanged lists have rank three, and the
original ambient rank equation supplies the remaining rank hypothesis. The
resulting map is complex linear, injective and satisfies the original compact
and Lie equivariance predicate.

This proof is internal derived content. Its representation theoretic inputs
are the proved generic, interlaced and endpoint Frobenius constructions, their
proved landing and uncertainty results, and induction in stages. It retains no
irreducibility, classification, landing or intertwining existence premise.
