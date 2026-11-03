# Actual homogeneous quotients by a prescribed Borel

Internal supporting construction by Worker 1438, derived from the published
Borel base-change and smooth-subgroup quotient APIs.

Over an algebraically closed field in arbitrary universe,
the reused `BruhatCovering.isParabolicSubgroup_of_isBorelSubgroup` proves that every
prescribed Borel inclusion is parabolic in the existing definition. The
algebra map from that field to its algebraic closure is bijective because it
is an integral extension of an algebraically closed field. The published
`IsBorelSubgroup.baseChange_of_bijective` therefore makes the actual
base-changed inclusion Borel. This inclusion itself, with identity factor,
is the geometric Borel witness required by `IsParabolicSubgroup`. No
preservation theorem for arbitrary extensions of algebraically closed fields
is needed.

Over any field, if the ambient group is smooth and affine,
`IsBorelSubgroup.homogeneousQuotient` chooses the actual homogeneous quotient
by the supplied Borel using `smoothSubgroupQuotientExistence`. Its published
`HomogeneousQuotient` structure retains a separated finite-type
quasi-compact scheme, a smooth surjective quasi-compact projection, and the
exact right-coset fiber condition on every relative test scheme. The chosen
subgroup is the given Borel, without a change of representative.

Over an algebraically closed field with connected ambient group,
`quotient_isProper_of_parabolicQuotient` applies the explicit hypothesis
`ParabolicSubgroupQuotientProperStatement` to any supplied homogeneous
quotient of that Borel. The final theorem specializes it to the chosen
quotient. Properness is conditional on that statement; this module neither
proves the general properness statement nor claims an unconditional proper
Borel quotient or a proof of `CentralizerBorelIntersectionStatement`.
