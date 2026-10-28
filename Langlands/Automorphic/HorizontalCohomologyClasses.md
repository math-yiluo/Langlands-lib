# Classes in actual automorphic horizontal cohomology

For an actual `OperatorRealization F n` over a number field in arbitrary
universe and positive natural rank, this internal unit specializes the
published generic horizontal class lemmas to the actual quotient
`S.HorizontalCohomology q`. Its coefficients are the existing complex module
`S.Space`, its cochains retain the full standard infinite compact group,
and every natural degree is covered.

The specialization fixes the actual compact Lie image, reduced compact
representation and compact coefficient action. The same actual conjugation
Lie equivalence, proved coefficient covariance and all-degree
`S.horizontalCochain_infinitesimal` supply every generic compatibility input.
There are no additional hypotheses on `S`.

`horizontalBoundaries_le_cycles` is the proved actual boundary inclusion.
`mem_horizontalBoundariesInCycles` identifies membership in its range inside
cycles exactly with boundary membership of the underlying horizontal
cochain.

`horizontalCohomologyClass_surjective` gives a closed horizontal
representative of every quotient class. `horizontalCohomologyClass_eq_zero`
identifies zero classes exactly with actual boundaries.
`horizontalCohomologyClass_eq_iff` identifies equality of classes exactly
with boundary membership of the difference of the underlying horizontal
cochains, with the first cochain minus the second.

`horizontalCoboundaryToCycles` abbreviates the same actual differential with
codomain restricted to cycles by the generic square-zero proof.
`horizontalCohomologyClass_coboundary` proves that every such actual
coboundary has zero class. No representative is chosen by these definitions
or proofs.

These declarations are direct abbreviations of proved generic lemmas,
with all actual actions and compatibility proofs fixed as above. Their
types are inferred from those proofs. Thus each proof alias has exactly
the specialized generic proposition; no proposition is merely assumed and
no proof is supplied by the consumer. In particular, the zero-class alias
proves

`S.horizontalCohomologyClass q f = 0 ↔ f.val ∈ S.horizontalBoundaries q`,

and the class-equality alias proves

`S.horizontalCohomologyClass q f = S.horizontalCohomologyClass q g ↔
  f.val - g.val ∈ S.horizontalBoundaries q`.

Inferring these types avoids repeating large instance comparisons through
the actual coefficient realization. The quotient and its canonical
operations are the imported ones; this module introduces no new group or
module instance.

The underlying generic proofs use the coefficient square-zero law, the
boundary inclusion and Mathlib's quotient projection and equality criteria.
For the coboundary-class proof the generic zero-class criterion is applied
and the input cochain itself is the boundary preimage. This source-free
internal specialization asserts no new external-literature comparison.
Finite adelic quotient action, full-operator transport and analytic or sheaf
comparisons remain separate. No nonvanishing theorem is asserted.

Authorship: Worker 2.
