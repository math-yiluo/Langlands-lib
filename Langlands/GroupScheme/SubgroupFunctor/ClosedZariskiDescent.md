# Effective Zariski descent of closed subgroup functors

This internal construction extends the published torus-specific argument in
`HomScheme/TorusSubgroupChartGluingProof.lean` to arbitrary closed subgroup
functors. It uses the Library's closed-subscheme gluing and representability
transfer results. It introduces no new assertion from external literature.

For a group scheme `G` over an arbitrary scheme `S`, `ClosedRepresentative F`
records a group scheme, a closed immersion into `G`, and representation of `F`
on every relative test scheme. `ofIsClosedRepresentable` chooses these data
from the existing existential predicate. The choice is noncanonical.

`isClosedRepresentable_of_openCover` proves that a subgroup functor `F` is
closed representable if its membership is Zariski local on every test scheme
and its pullback to every member of an open cover of `S` is closed
representable. No smoothness, affineness, finiteness or separation condition on
the base or ambient group is imposed.

The proof chooses a local closed representative and converts its all-test
membership into factorization of absolute scheme maps. Pulling the base cover
back to the ambient scheme gives local closed subschemes. The published
`Scheme.ClosedSubschemeGluing.exists_isClosedImmersion` glues them using
restriction stability and Zariski locality of absolute membership. The
published representability transfer then equips this global scheme with its
group scheme structure. `closedRepresentativeOfOpenCover` chooses the
resulting actual closed subgroup.

For an open cover `𝒰` and local subgroup functors `H`, the matching hypothesis
is exactly the published all-test condition `IsMatching 𝒰 H`.
`isClosedRepresentable_descentSubgroup` applies the result to the published
`descentSubgroup 𝒰 H`. Represented subgroups are Zariski local, and the
published matching theorem identifies each local base change with `H i`.
`closedRepresentativeOfMatching` chooses an actual global representative.
Its restriction represents each given `H i`, by
`IsRepresentedBy.baseChange` and `baseChange_descentSubgroup`.

These constructions establish Zariski descent of the closed subgroup
condition only. Descent of smoothness, the relative Levi predicate and
descent along other topologies are separate obligations.
