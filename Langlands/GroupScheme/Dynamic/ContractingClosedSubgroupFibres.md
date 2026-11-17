# Unipotent field fibres of closed contracting subgroups

Worker 851.

This internal consequence of the published dynamic-subgroup theory applies
to a smooth affine group scheme `G` over `Spec R`, for an arbitrary
commutative ring `R`. Let `χ` be a cocharacter of `G` and let `j : H ⟶ G`
be a closed subgroup whose subgroup functor lies in `Dynamic.unipotent χ`.
Then the base change of `H` along every field-valued point of `Spec R` is
unipotent, in the Library's representation-theoretic sense. In particular,
all geometric fibres of `H` are unipotent. No smoothness or connectedness
of `H` is asserted or assumed.

Factor `j` through the affine representative `U` of the dynamic unipotent
subgroup. The factor is a closed immersion because its composite with the
closed inclusion of `U` is the closed immersion `j`. The group `U` is smooth
over `R` by `dynamicSmooth_ring`. After base change to a field, the dynamic
base-change theorem shows that `U` still represents the corresponding
contracting subgroup. The published `dynamicUnipotentUnipotence` proves it
is unipotent. The base-changed factor is a closed immersion, so
`unipotentClosedSubgroup` gives unipotence of the field fibre of `H`.
Taking the field-valued point `geometricPoint` yields the last theorem.

This is a generic supporting lemma for the directly spanned root subgroup
clause of `AffineSplitRootSubgroupSpanningStatement`; it does not establish
the subgroup's existence or connectedness.
