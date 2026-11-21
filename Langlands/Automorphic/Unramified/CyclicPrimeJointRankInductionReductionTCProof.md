# Strong induction over a totally complex base

`Langlands.Automorphic.Unramified.cyclicPrimeJointRankInductionReductionTC`
proves `CyclicPrimeJointRankInductionReductionTCStatement` with the four
independent field and spectral-presentation universes. Its premise is the
totally complex analytic rank-step statement. The separate
`NumberField.IsTotallyComplex F` instance is available when applying that
step to the fixed base field and extension.

The motive for `Nat.strong_induction_on` gives the conjunction of going up
and going down at rank `n` under `0 < n`. For every `0 < k < n`, the
going-up step uses the second projection of the joint result at `k`, and
the going-down step uses its first projection. The pair of new conclusions
gives the joint result at `n`.

This is the totally complex form of the strong-induction assembly for the
existence clauses of Arthur–Clozel, *Simple Algebras, Base Change, and the
Advanced Theory of the Trace Formula* (1989), III.4.2(a), (b), (d) and
(e), printed pp. 202–210.
[Published rank-step and reduction statements](CyclicPrimeJointRankInductionStatement.md)
