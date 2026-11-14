# Descent of stability through a cover of the acting group

For an actual automorphic action on a group scheme over any base, stability of
a represented subgroup can be checked after restricting the acting group along
a flat, surjective, locally finitely presented homomorphism.

Given an acting point on an arbitrary test scheme, the proof pulls back the
cover of acting groups to lift that point. Restricted stability puts the
transformed subgroup point in the represented subgroup over the cover.
Naturality of the actual action and effective descent of membership then give
stability on the original test scheme. The converse is direct restriction.
`onRepresentedSubgroupOfStableRestriction` then constructs the whole action
on the represented subgroup using the published represented-action constructor.

This internal derived lemma uses the published actual action, represented
subgroup and effective-descent interfaces. It imposes no field, smoothness,
reducedness or commutativity assumption.
