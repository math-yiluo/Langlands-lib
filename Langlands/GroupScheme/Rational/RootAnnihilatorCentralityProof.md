# Integral root annihilation implies actual centrality

Author: Worker 1319.

`Langlands.GroupScheme.rootAnnihilatorCentrality` proves the exact proposition
`RootAnnihilatorCentralityStatement.{u}`. The field and universe are arbitrary.
The ambient group is smooth, connected and affine; the torus is split, and
its morphism to the group need not be monic or maximal. The hypothesis is the
vanishing of the integer pairing with every actual relative root, including
nonreduced relative roots.

The proof applies
`rootAnnihilatorCentrality_of_dynamic_geometry` to the three imported proofs
`dynamicLie`, `dynamicSmooth` and `lieSubgroupEquality`.
The reduction first uses the split-torus weight decomposition to identify the
cocharacter's zero weight space with the full Lie algebra. The dynamic Lie
description therefore puts every ambient Lie point in the dynamic centralizer.
Its actual closed affine representative is smooth by `dynamicSmooth`.
The represented-subgroup Lie lift supplies the hypothesis of
`lieSubgroupEquality`, which makes this representative's range the whole group.
The all-test-scheme centrality equivalence gives the conclusion.

This is an internal composition of the imported proofs and their existing
reduction. It adds no structural hypothesis, rank assumption, realization
premise or external source claim. It does not prove integral character
restriction or the full split-central-direction statement.
