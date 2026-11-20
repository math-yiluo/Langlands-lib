# Reduction of cyclic regular induction

`Langlands.Automorphic.Unramified.CyclicRegularInductionReductionStatement.{uF,uE,uV,uW}`
concludes the published `CyclicRegularInductionStatement` from three premises.

| Premise | Role |
| --- | --- |
| `CyclicRegularInductionExistenceStatement` | Choose an actual unitary lower cusp with the required rank and attached weak induction. |
| `CyclicNormKernelUnramifiedOrderStatement` | At each retained base place the local value of `η` has order equal to each residue degree above it. |
| `CuspidalEulerConstituentRecoveryStatement` | Use the singleton case to identify two actual cuspidal classes with matching attached Euler factors. |

`CyclicRegularInductionReductionTCStatement` concludes
`CyclicRegularInductionTCStatement` from the totally complex existence and
Euler recovery premises and the same arithmetic character-order premise.
Both reductions have the four independent universes of the original
statements, including the instantiation `.{0,0,uV,uV}`.

Arthur and Clozel, *Simple Algebras, Base Change, and the Advanced Theory
of the Trace Formula* (1989), Chapter III, Theorem 6.2 and Lemma 6.4,
printed pp. 215–218, supply the induction and regular-orbit results from
which this reduction is derived. For the self-twist step, use the
induced denominator in Definition 6.1. Multiplying the lower eigenvalues
by the local character value substitutes `η_v(ϖ_v) X` for `X`. This fixes
each induced polynomial factor in `X^f` because `η_v(ϖ_v)^f = 1`. The
published determinant-twist construction attaches this scaled spectrum
to the actual twist of the lower class. Euler recovery identifies the
class and its twist, giving the full-class finite-order twist relation.

For uniqueness take any cuspidal competitor of the stated rank weakly
induced from the same upper class. The two upper presentations agree at
almost all places. On a common cofinite set downstairs the weak induction
identities give equality of the two lower denominators. Apply the same
singleton recovery, the Library form of the comparison in III.(2.4),
printed p. 200. The competitor requires no unitarity assumption and the
chosen witness comes from the actual existence premise. No transfer
comparison at a deleted finite place or an infinite place enters this
reduction.
