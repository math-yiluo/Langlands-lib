# Conditional assembly of the exact relative-root vector statement

This internal reduction proves `RootSubgroupVectorReductionStatement` from the
Library's actual constructions and the focused support modules
`RelativeRootMultiples`, `RootSubgroupVectorTransport`, `WeightSupportCongruence`,
`WeightSupportVanishing` and `RootSubgroupCentrality`. The reused support and
centrality modules were authored by Worker 1303; the arithmetic, coordinate
transport and assembly were authored by Worker 1287.

The statement keeps five exact existing general propositions as premises:
`RelativeRootSystemStatement`, `SemigroupRealizationStatement`,
`SemigroupCommutatorStatement`, `CyclicRootFunctorComparisonStatement`, and
`CyclicWeightFiltrationStatement`. Its conclusion is the exact existing
`RootSubgroupVectorStatement`. It does not prove any of these five premises and
does not discharge the final task unconditionally. The field and scheme universe
remain arbitrary, and there is no reduced-root or quasi-split assumption.

Given a connected reductive group and a maximal split torus, the root-system
premise and the arithmetic lemma exclude every multiple n alpha with n at least
3. The cyclic comparison identifies the first conjugation filtration term with
the actual root subgroup. For any monomorphic representative, the r = 1 cyclic
filtration premise produces a represented fppf quotient by the inverse image of
the second term, and gives natural single-weight vector coordinates on its
target. Forgetting the weight and uniqueness assertions makes the target a
vector group.

If 2 alpha is absent, the second filtration term is trivial. The inverse image
under the representative is trivial because that representative is a
monomorphism. The fppf quotient by the actual trivial kernel is an isomorphism,
so its source is a vector group. This proves the branch for every representative.

In the doubled-root branch, the centrality helper gives the actual inclusion and
commutation on all scheme tests. Ambient weight support outside the first two
multiples is absent, so the second filtration term equals the first term for
2 alpha, hence the actual doubled-root subgroup. Rewriting the cyclic quotient's
kernel equality therefore gives precisely the inverse image of that subgroup
under the chosen representative. The quotient map is flat, surjective and
locally of finite presentation, and its target has the natural vector
coordinates obtained above. The proof uses no surjectivity assertion for the
point groups of original test schemes.
