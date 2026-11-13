# Transport of pro-p subgroups through topological group isomorphisms

This internal prerequisite transports the existing
`Langlands.Cohomology.IsProPSubgroup` predicate without changing the
topology on any subgroup. The ambient groups may have independent
universes and arbitrary topologies.

`openNormalComapOrderIso e` constructs an order isomorphism from the
open normal subgroups of the target of a continuous multiplicative
equivalence `e` to the open normal subgroups of its source. Its forward
map is `openNormalComap` along `e`; its inverse uses `e.symm`.
The two inverse identities follow from the inverse identities of `e`.
Order reflection follows by applying an inclusion of inverse images to
the inverse image of each target element.

`IsProPSubgroup.of_continuousMulEquiv` assumes a pro-p subgroup `H` and
a continuous multiplicative equivalence from the actual subgroup type
`H` to another subgroup type `K`. It proves that `K` is pro-p.
Primality is inherited from `H`. The underlying homeomorphism
transports compactness and total disconnectedness. For an open normal
subgroup `N` of `K`, the proof pulls `N` back to `H`. The pro-p
predicate on `H` supplies a p-power killing the class of `e.symm y`.
Applying `e` shows that the same p-power kills the class of `y` modulo
`N`. Quotient induction proves the p-group condition on the whole
quotient. No abstract p-power torsion assumption on `H` is made.

For `H ≤ K` in a common ambient group, `IsProPSubgroup.subgroupOf`
and `IsProPSubgroup.of_subgroupOf` give both directions between the
pro-p property of `H` in the ambient group and that of `H.subgroupOf K`
inside `K`. They use Mathlib's
`Subgroup.subgroupOfContinuousMulEquivOfLe`, which preserves the
inherited subgroup topology.

The provenance is elementary transport from the published pro-p
predicate, `openNormalComap`, Mathlib's subgroup equivalence and
homeomorphism transport lemmas. The result supplies no integral-model
pro-p property, reduction-map continuity or finite reductive
classification. These remain separate inputs to the proof of corrected
KP Proposition 13.5.2.
