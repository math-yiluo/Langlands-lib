# Split-torus rigidity without split unipotent subgroups

Author: Worker 1478.

This internal construction works over every field in arbitrary universe `u`.
It uses actual group schemes and equalities on every relative scheme test.

`HasNoNontrivialSplitUnipotentSubgroup G` says that every smooth connected
unipotent closed subgroup of `G` satisfying the existing finite Ga-series
splitness predicate has bottom full image. It makes no normality assumption
on that subgroup. This is a new explicit condition, not a definition of
woundness or of triviality of the split unipotent radical. No equivalence
with either of those conditions is asserted.

For any actual multiplicative-group action on a smooth affine `G`,
`AutomorphicAction.unipotent_eq_bot_of_no_split_unipotent_subgroup` applies
the condition to the actual split contracting subgroup from
`Dynamic.SplitContractingSubgroup`. Its closed inclusion represents the
original action's full identity-limit functor, so that functor is bottom.
The accompanying positive-weight lemma uses the already proved dynamic
Lie criterion to identify its tangent submodule with the intrinsic
positive weight span. The tangent submodule of bottom is bottom.

For an actual split-torus action `b` on a smooth connected affine group,
`fixedSubgroup_eq_top_of_cocharacter_unipotent_eq_bot` first assumes only
that the contracting functor of every cocharacter-restricted action is
bottom. Given a nonzero character, the published positive-pairing theorem
supplies a cocharacter whose pairing with it is a positive natural number
`D`. The exact cocharacter weight-sum theorem embeds that character's
weight space in the restricted action's positive span, using the index
`D - 1`. That span vanishes by the preceding tangent lemma. Thus every
nonzero character weight vanishes. The published split-torus Lie
decomposition implies that weight zero is the whole Lie algebra.

The existing smooth closed representative of the full fixed subgroup has
that zero-weight tangent image. The published smooth closed subgroup
equality theorem makes its image the whole connected ambient group.
This proves equality of the fixed subgroup functor with top, including
nonaffine and nonreduced relative tests. Evaluating this full fixedness
at each identity refinement proves that the actual action morphism
equals the second projection. This is the result
`eq_trivial_of_cocharacter_unipotent_eq_bot`.

Finally, `eq_trivial_of_no_split_unipotent_subgroup` supplies the contracting
hypothesis by applying the first lemma to every cocharacter restriction.
It proves actual triviality for every split-torus action on such a smooth
connected affine group, with no perfectness, characteristic or field-size
restriction. Unipotence of the ambient group is not needed.

The provenance is internal. The implemented proof combines published
contracting-subgroup geometry, torus-action unipotence and splitness,
positive pairings, exact intrinsic Lie weight decompositions and smooth
fixed-subgroup equality. It does not prove the absence condition for a
wound quotient or for the ordinary unipotent radical modulo its split
radical. Split-radical product replacement and the host rational-lifting
statement remain separate obligations.
