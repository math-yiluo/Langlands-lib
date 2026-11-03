# Centrality of the doubled relative-root subgroup from cyclic tails

`HasCentralDoubleSubgroup i a` means that the actual subgroup functor for
`2*a` is contained in the subgroup functor for `a`, and that points of the
former commute with points of the latter on every scheme over the base.
The definition is over an arbitrary base scheme. It is the inclusion and
centrality part of the published `RootSubgroupVectorStatement`, without
asserting a vector structure or a represented quotient.

The proofs work over an arbitrary field at every universe. They retain
the exact `CyclicRootFunctorComparisonStatement` as a hypothesis, alongside
smoothness of the ambient affine group and splitness of the acting torus.
The comparison identifies the first cyclic tail for `a` with the actual
root functor, and likewise for `2*a`, which is nonzero by the published
`IsSplitTorus.nsmul_ne_zero`. The first tail for `2*a` lies in the second
tail for `a`; the latter lies in the first tail for `a`. This gives the
claimed subgroup inclusion.

Centrality additionally assumes the exact `SemigroupRealizationStatement`
and `SemigroupCommutatorStatement`, and the exclusion of relative roots
`n*a` for every natural coefficient `n >= 3`. The conjugation support
comparison from `WeightSupportVanishing` converts this exclusion into
absence of ambient weights. The second tail for `a` then equals the first
tail for `2*a`, by `weightFiltration_two_eq_double` from
`WeightSupportCongruence`, while the third tail for `a` is trivial by
`weightFiltration_eq_bot_of_noRelativeRoots`. The commutator bound places
the commutator of a point of the second tail and a point of the first tail
in the third tail. Its triviality proves commutation of the original
points on every test.

The provenance is the actual cyclic-tail definitions and the imported
support congruence, root-support comparison, vanishing and group-theoretic
commutator consequences just named. This is a conditional assembly of
those results; none of the three source statements or the higher-root
exclusion is proved here. In particular the full root-vector and fppf
quotient target remains open.
