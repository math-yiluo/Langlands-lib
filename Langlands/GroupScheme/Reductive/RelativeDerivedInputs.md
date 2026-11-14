# Inputs for the relative derived group

Author: Worker 672.

This module isolates two inputs to the unchanged published
`Langlands.GroupScheme.RelativeDerivedGroupStatement`. Neither input is proved
here.

`RelativeDerived.IsAdmissible d` names exactly the local admissibility predicate
in that statement: the homomorphism `d : D ⟶ G` is a closed subgroup, its
all-test range is normal, `D` is reductive with semisimple geometric fibres,
and there is an fppf quotient of `G` by that range whose target is a relative
torus. The quotient is the existing `RelativeRoot.IsFppfQuotient`; in particular,
the predicate adds no quasi-compactness hypothesis.

`RelativeDerived.LocallyCommutator x` is the point condition in part (2) of the
published statement. It uses a jointly surjective cover of the test scheme
whose members are flat and locally of finite presentation. On each cover
member the restriction of `x` belongs to the abstract group commutator
subgroup. Membership permits a finite product of commutators and their
inverses; it does not require a single commutator.

`RelativeDerivedGroupExistenceStatement.{u}` asserts that, for every scheme
`S` and reductive group scheme `G` in universe `u`, some group scheme `D`
and homomorphism `d : D ⟶ G` satisfy this admissibility predicate.
`RelativeSemisimpleFppfPerfectStatement.{u}` asserts that, for every
reductive group scheme `D` with semisimple geometric fibres, every point
on every test scheme over its base satisfies `LocallyCommutator`.
There are no extra hypotheses on the base or the test scheme.

The provenance is derived: these are the geometric existence assertion and
the semisimple fppf-perfectness input in Brian Conrad, *Reductive group
schemes* (2014), Theorem 5.3.1, pp.160–163, especially the final paragraph on
p.163. The registered source is `conrad-2014-reductive-group-schemes`,
SHA-256 `1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
The admissibility and local-point formulations are internal named copies of
the already published target, so their names are not claimed to occur in the
source. This module supplies statements of those inputs and elementary
supporting proofs, rather than a construction of the relative derived group.

The helper `effectiveEpiFamily_fppfCover` follows from subcanonicity of
Mathlib's fppf topology: each representable is a sheaf on the covering
presieve, which is therefore effective epimorphic.
`fppfCover_hom_ext` applies joint effective epimorphy to the underlying scheme
maps and then extensionality in the over category. Neither lemma requires
quasi-compact cover members.

`LocallyCommutator.map` uses the induced homomorphism on the group of points
and functoriality of the abstract commutator subgroup.
`LocallyCommutator.comp_eq_one` observes that the image of the commutator
subgroup in a commutative group is trivial, applies that observation after
the cover, and descends equality using `fppfCover_hom_ext`.
These helpers are proved unconditionally and do not assume either input
statement.
