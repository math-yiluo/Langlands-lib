# Strong induction from the strict prime cyclic rank steps

`Langlands.Automorphic.Unramified.cyclicPrimeJointRankInductionReduction`
proves `CyclicPrimeJointRankInductionReductionStatement` with the four
independent universes for the two fields and the two spectral presentations.
It takes the unrestricted analytic rank-step statement as its premise.

Fix the extension, cyclic generator and norm-kernel character. Apply
`Nat.strong_induction_on` to the total rank `n` with the motive that, if
`0 < n`, both going up and going down hold at rank `n`. For each
`0 < k < n`, the second component of the induction hypothesis supplies
going down at `k` for the going-up step. The first component supplies
going up at `k` for the going-down step. Pair the two conclusions at `n`.
At rank one the lower positive ranks form an empty range.

The rank-step interface comes from the existence parts of Arthur–Clozel,
*Simple Algebras, Base Change, and the Advanced Theory of the Trace
Formula* (1989), III.4.2(a), (b), (d) and (e), printed pp. 202–210.
The proof formalizes the strong-induction assembly from that interface.
[Published rank-step and reduction statements](CyclicPrimeJointRankInductionStatement.md)
