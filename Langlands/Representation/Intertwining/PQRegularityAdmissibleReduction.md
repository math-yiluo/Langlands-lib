# The PQ-regularity lemma from finite-length admissibility

This is an internal reduction toward the exact Renard VII.3.3 target
`PQRegularityLemmaStatement.{u,v}` (Renard 2026, Lemma of VII.3.3, printed pp.233–235 / PDF pp.239–241).
It retains exactly one global premise, the published
`RationalPointsFiniteLengthAdmissibleStatement.{u,v}` (finite-length smooth
representations of the rational points of a connected reductive group are
admissible; the direction of Renard VI.6.3 used here), and concludes the
unchanged `PQRegularityLemmaStatement.{u,v}`. This premise is not proved by this
unit, and the unit does not establish the unconditional regularity target.

`PQRegularityAdmissibleReductionStatement` is the implication
"`RationalPointsFiniteLengthAdmissibleStatement` implies
`PQRegularityLemmaStatement`" at the same field universe `u` and
representation-carrier universe `v`, and
`pqRegularity_admissible_reduction` proves it.

## Provenance

The statement is internal: it is not a translation of a single source
assertion. It records that, in the proof of Renard VII.3.3, the only input
not yet proved in the Library is the admissibility of the finite-length
representation `σ` of `M(F)`. The Library's earlier conditional assembly
`pqRegularity_finiteLength_reduction` (module `PQRegularityFiniteLength`)
retains instead two premises, finite length of Levi Jacquet modules (VI.6.4)
and of Levi induction (VI.6.2). The present reduction avoids both.

## Proof

The first two clauses of the target come unconditionally from
`pqRegularity_predecessorCriteria`.

For the third clause, let `σ` have finite length and assume the disjointness
of the exponents of `σ` from the generalized weights of the split component on
every strict-predecessor piece.

1. `exists_pqRegularity_pieceFiltration` enumerates all strict predecessors
   `c i` of the identity double coset and gives a filtration of the actual
   regularity quotient whose `i`-th grade is naturally isomorphic to the full
   geometric piece functor `i^M_{Q'} ∘ ι ∘ r^M_{P'}` of the datum `D (c i)`.
   `pieceFunctor_isSmooth` gives smoothness of each piece.
2. `finite_splitComponent_actionQuotient` gives the finite-dimensional faithful
   action quotient of the split component on `σ` itself, from finite length
   alone.
3. The premise, applied to the connected reductive Levi `M`, makes `σ`
   admissible. Finite length makes the group-algebra module of `σ`
   Noetherian, hence finitely generated.
4. For every strict predecessor `w`, the proof generalizes the datum `D w h`
   to a local datum `E`. The proved `arbitraryParabolicJacquetAdmissibility`
   (Renard VI.6.1), transported by `isAdmissible_comp_continuousMulEquiv` along
   `leviPointsEquiv`, makes the Levi Jacquet module of `σ` along `E`'s
   parabolic admissible, and the proved `leviJacquetFiniteType` (Renard VI.1.3)
   makes it finitely generated. `exists_isCentralSplitTorus_factor` factors
   the split component through the datum's target Levi `L'`, and
   `GeometricLemmaIntersectionDatum.finite_actionQuotient_piece` then gives the
   finite-dimensional action quotient on the full piece.
5. With these finiteness instances, `pqRegularity_of_disjoint_weights`
   concludes `IsPQRegular`, after reindexing the disjointness hypothesis along
   the predecessor enumeration.

The theorem uses `set_option maxHeartbeats 1200000` and
`backward.isDefEq.respectTransparency.types false` for elaboration only.
No other premise is added; all quantifiers of the target are kept.
