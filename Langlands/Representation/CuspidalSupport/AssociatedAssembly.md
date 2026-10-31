# Conditional assembly of the associated Jacquet filtration

Author: Worker 193. This is an internal helper for
`AssociatedJacquetFiltrationTheorem`; it is not a proof of that unconditional
published target. The helper assumes the published geometric lemma for the
given rank, its three associated-piece component propositions, and the
zero-factor deletion proposition. The companion `AssociatedProof` module
discharges these inputs with published proofs.

The proof evaluates the geometric lemma's actual functor filtration at the
smooth quasicuspidal input. It composes the gluing permutation with the supplied
enumeration of minimal representatives. Each natural graded isomorphism is
evaluated at that input and turned into an actual representation equivalence.
The vanishing component then shows that every nonconjugating graded quotient
is zero. Applying deletion to the predicate of conjugating the entire Levi
retains every conjugating occurrence, including occurrences whose carriers
are zero. Restricting the enumeration to this predicate gives a bijection with
all `MinimalConjugatingPermutations`.

For each retained quotient, the deletion equivalence, the evaluated geometric
isomorphism and the piece-to-transport equivalence compose to identify it with
the corresponding whole-Levi transport. The published invariance lemma
`isLeviQuasicuspidal_iff_of_equiv` transfers transport quasicuspidality to the
actual quotient. The helper returns this filtration, its full index bijection,
all transport equivalences and quasicuspidality of every graded quotient.
Quasicuspidality of the ambient representation still requires finite-filtration
closure; the rank-zero branch is supplied separately in `AssociatedRankZero`.

This is internal bookkeeping using the exact published interfaces underlying
the BZ77 Corollary 2.13(c) consumer. It introduces no geometric or analytic
claims beyond its explicit prerequisite hypotheses. The component propositions
are meaningful at any rank, so the helper itself needs no positive-rank
hypothesis; eventual use of the aggregate geometric results is at positive rank.
The field and input-carrier universes remain independent; the evaluated and
compressed quotient carriers are in `max uF uV`.
