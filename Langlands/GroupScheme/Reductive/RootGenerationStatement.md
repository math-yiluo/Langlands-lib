# Generation of semisimple groups by actual root subgroups

`Langlands.GroupScheme.SemisimpleRootGenerationStatement.{u}` states the
closed-subgroup form of generation by root groups over algebraically closed
fields of arbitrary characteristic. For an actual semisimple group scheme
`G`, a closed inclusion `t : T.toGrp ⟶ G` which is both a split subtorus and
a maximal torus, and any actual closed subgroup `d : D ⟶ G`, containment
of `RelativeRoot.subgroup t α` in the full range of `d` for every actual
relative root `α` implies `SubgroupFunctor.range d = ⊤`.

The original is J. S. Milne, *Algebraic Groups: The Theory of Group Schemes
of Finite Type over a Field*, corrected reprint (2022), registered source
`milne-2022-algebraic-groups`, Proposition 21.49(a), printed p.439
(PDF p.450). The proposition says that a split semisimple group is generated
by its root groups. Its proof obtains the coroot tori from the rank-one
identities and then obtains the entire maximal torus from the finite-index
root lattice. The proposition is used in the rewritten proof of
Theorem 21.51 on printed p.440. The registered 2017 and 2022 author errata
were read: the former directs readers to the rewritten 2022 proof of
Theorem 21.51, and the latter makes no correction to Proposition 21.49.

The Lean formulation uses the published intrinsic orbit-extension root
functors, the published Lie-weight relative roots, and the published
definition of semisimplicity. In this algebraically closed split setting
these express the source's absolute root groups and roots. Proving the
statement includes any structural comparison needed to use those
definitions; no chosen root-group realization is a premise. The explicit
affineness instance is supplied by semisimplicity. Splitness and maximality
are properties of the given actual torus inclusion, rather than additional
root-datum data.

Both containment and the conclusion quantify over all test schemes,
including nonreduced ones. The closed-subgroup generation formulation is
weaker than pointwise abstract generation and does not assert that arbitrary
test-valued points are finite products of root points. This file defines a
proposition target; it supplies no proof of root-group generation,
almost-simple generation, or decomposition.
