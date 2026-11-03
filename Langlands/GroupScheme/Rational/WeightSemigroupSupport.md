# Actual weight support and semigroup subgroup order

Author: Worker 1312.

This internal API is derived from the published definitions in
`Rational.WeightSemigroup` and `Rational.RootSubgroupStructureStatement`.
It proves no representability, smoothness, maximality or exact dynamic
comparison theorem.

`SemigroupWeightSupportLE b A A'` means that membership in `A` implies
membership in `A'` for every character in the ambient action weight support.
It is a relation between semigroups restricted to weights that actually occur;
it includes the zero character when that weight occurs. It is independent of
any assertion that the generated subgroup has a smooth representative.

`actionWeightSupport_mono` transfers the same nonzero tangent vector through
an inclusion of subgroup functors. `mem_actionWeightSupport_top` identifies
ambient support with nonvanishing of the actual action weight space.

`semigroupSubgroup_mono_on_weightSupport` needs the source semigroup to imply
the target semigroup only on actual ambient weights. For each smooth connected
stable closed source generator, its support is also ambient support. Thus the
same generator is admissible for the target. The point-group closure defining
the source subgroup lies in the target subgroup on every test scheme.

`weightSupport_inter_subset_of_hasLieImage` assumes explicitly that a subgroup
has the exact semigroup Lie image. A nonzero vector in an allowed ambient
weight space belongs to the selected supremum, hence to the subgroup on the
dual-number test. It therefore witnesses the same weight in that subgroup's
support.

`semigroupSubgroup_le_iff_on_weightSupport` combines these arguments. Its
necessity direction explicitly assumes the exact source Lie image and the
target subgroup's support bound. It transports a nonzero vector along the
all-test inclusion and applies that bound. Its sufficiency direction is the
unconditional generator argument. These hypotheses are visible in Lean;
this is not an unconditional proof of the source semigroup realization or of
`RelativeRootSignInclusionsStatement`.

No assumption of a nonempty or reduced root system, reductivity, finite type,
or maximality is made. The ambient field and the actual action retain their
original universe. Zero weights are included whenever their weight space is
nonzero.

The support monotonicity theorem `actionWeightSupport_mono` is reused from
`SemigroupClosure`.
