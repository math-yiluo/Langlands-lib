# Joint rank induction for prime cyclic cuspidal realization

The propositions are in `Langlands.Automorphic.Unramified`. All weak
transfer relations retain the four independent universes `uF uE uV uW`,
for the two fields and the two spectral-presentation carriers.
The matrix rank of `CuspidalOperatorRealization F r` is `r + 1`.

`CyclicPrimeGoingUpAtRank` expresses the existence in (a) and (b), for an
actual unitary lower cusp of rank `n`. For a cusp without the supplied
norm-kernel determinant self-twist, the attached upper witness is an
actual unitary cusp of the same rank, stable under the generator. For a
self-twist cusp, the witness is an actual unitary cusp of rank `n/l` with
nontrivial generator orbit. The full orbit is required to give unitary
isobaric data and an attached weak base change of the lower singleton.

`CyclicPrimeGoingDownAtRank` expresses the realization in (d) and (e).
A stable upper cusp of rank `n` has an actual unitary lower cusp with the
weak transfer of classes. For an upper cusp of rank `m + 1` whose class
moves under the generator, the same total rank means `n = (m + 1) l`.
Its full orbit has an actual unitary lower cusp with the weak transfer of
isobaric data. The definition keeps the existence clauses only.

`CyclicPrimeRankStep` says that going up in rank `n` needs going down at
ranks `0 < k < n`, and that going down in rank `n` needs going up at those
ranks. In the source going up uses a fixed smaller upper block through (d)
or a smaller **total** orbit size through (e). The full-size orbit in (a)
and the full-size singleton in (b) are treated by the self-pair pole orders.
Going down applies (a) or (b) to a minimal-exponent lower cuspidal block in
proper support. Its rank is strictly less than `n`. The Rankin–Selberg
comparison subsequently rules out this support. Neither implication
assumes a same-rank conclusion of the other.

`CyclicPrimeJointRankStepStatement` quantifies the step over actual number
fields with their compact adelic quotients, a prime-degree Galois extension,
a generator and a Hecke character with norm kernel. The `TC` form inserts
`[NumberField.IsTotallyComplex F]`. The two `CyclicPrimeJointRankInduction`
statements assert the resulting existence in both directions at every
positive rank. Each `Reduction` proposition takes only its own analytic
step as a premise and gives that all-ranks conclusion by strong induction.
The instance of the norm-kernel character can be obtained from the published
`CyclicNormKernelCharacterStatement` and its proof.

These are derived interfaces for Arthur and Clozel, *Simple Algebras, Base
Change, and the Advanced Theory of the Trace Formula* (1989), III.4.2(a),
(b), (d), (e), printed p. 202, and their proofs on pp. 203–210. Registered
source `arthur-clozel-1989-base-change`, SHA-256
`c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
The step and the all-ranks conclusions are propositions for later proofs.
