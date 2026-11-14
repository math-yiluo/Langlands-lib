# Reducing norm-one centralizer boundedness to Henselian quasi-splitness

Worker 336. This internal reduction for Task 6432 combines the proved torus
boundedness specialization with published results about quasi-split groups,
maximal split torus conjugacy, and the actual maximal unramified field. It
states and proves an implication, retaining the unproved generic Henselian
quasi-splitness theorem as an explicit premise.

`CentralizerNormOneBoundedHenselianReductionStatement` is the proposition
`HenselianDiscreteQuasiSplitStatement → CentralizerNormOneBoundedStatement`,
at arbitrary universe. The theorem
`centralizerNormOneBounded_of_henselianDiscreteQuasiSplit` proves this
implication. It does not establish its premise or prove the target outright.

The first auxiliary theorem applies to any field and any supplied
representative of the full centralizer of a maximal split torus in a
quasi-split group. The published existence theorem supplies one maximal split
torus whose centralizer is represented by a torus. Rational conjugacy of
maximal split tori transports this representation to the supplied maximal
split torus. The transport theorem compares the full subgroup functors on
every test scheme, including refinements. Uniqueness of represented subgroups
then identifies the supplied centralizer group scheme with the transported
torus. Torus structure is invariant under this isomorphism. This argument
does not replace the supplied centralizer by an unrelated choice.

`centralizerNormOneBounded_of_unramifiedQuasiSplit` applies this result to
the group and maximal split torus in each supplied building datum. The
previously proved `centralizerNormOneBounded_of_isTorus` then gives the exact
image of the integer-normalized character kernel, with the prescribed
`fixedFieldValued` valuative relation.

Finally, the published `unramifiedQuasiSplit_of_henselianDiscrete` supplies
unramified quasi-splitness from the displayed generic premise. Its field
inputs are the proved surjectivity of the constructed integer valuation,
the Henselian property of its valuation ring, and algebraic closedness of
its residue field. No completeness or local-field instance on
`inertiaFixedField F` is introduced.
