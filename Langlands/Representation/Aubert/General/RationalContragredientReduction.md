# Rational-point specialization of the exact-K0 duality reduction

This internal module specializes `ContragredientReduction` to the actual
standard rational-point family of the published
`RationalContragredientCommutationStatement`. It supplies a sufficient
prerequisite and proves its implication to the unchanged target. It does not
prove the prerequisite or the final unconditional commutation proposition.

`standardContragredientTermComparison` is the generic
`ContragredientTermComparison` on `parabolic i ν`, `levi i ν`, and
`unipotent i ν`. The indices are literally `Finset (SimpleRoot i ν)`, with
the existing finite enumeration. The semidirect decompositions and the
normalized induction and Jacquet functors are the published actual
constructions. Finite-length preservation and the topological hypotheses
supply `standardParabolicFiniteLength`; the smooth dual finite-length
premise supplies the finite-length proofs for its classes.

The comparison asks for a cardinality-preserving equivalence of these
indices and equality of actual exact-K0 classes between a term on the
smooth dual and the smooth dual of a reindexed term. Its purpose is to
allow the representation-theoretic argument to use associated standard
Levi subgroups. This module does not construct or justify that associated
Levi comparison. In particular, it does not replace it with the mere
existence or finite length of the smooth dual.

`rationalContragredientCommutation_of_standardTermComparison` applies the
proved generic reduction. `RationalContragredientTermComparisonStatement`
closes this additional prerequisite over precisely the field, connected
reductive group, maximal split torus, generic cocharacter, canonical
`pointTopology`, topology premises, structural inputs and finite-length
premises of the published target. It retains independent universes `u`
and `v`, with representation carriers in `max (u + 1) v`. There is no
restriction to characteristic zero, split or quasisplit groups, or a
nonempty root type.

`rationalContragredientCommutation_of_termComparison` proves that a proof
of this closed prerequisite would prove the exact original proposition,
with no further parameters. This is a conditional reduction, not a proof
of that proposition. The original target and its imports are unchanged.
No compatibility package or admissibility premise has been added to the
original target.

The proof dependencies are
`contragredientCommutation_of_termComparison`,
`standardParabolicFiniteLength`,
`simpleRelativeRootFintype`, the published definitions of
`rationalAlternatingOperator` and `contragredientK0`, and
`compactOpenCofinal_of_nonarchimedean`. The generic reduction's Markdown
gives its generator-level proof dependencies. No Langlands
classification, character independence, geometric lemma, adjointness, or
cuspidal-support theorem is used in the reduction. Such dependencies in
any eventual proof of the new class-comparison statement remain to be
reported separately. Provenance is internal: this is a reduction of the
published actual-family constructions, not a new claim attributed to the
literature.

The local topology instance is named `rationalContragredientReductionPointTopology` to avoid
generated-name collisions when rational-family modules are imported together.
Its defining value remains `pointTopology`.
