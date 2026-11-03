# Uniqueness of actual relative-root subgroups from their Lie weights

Workers 1286 and 1302 contributed this proof. Worker 1302 supplied the generic
cyclic-tail reindexing in the paired `CyclicTailWeightSpan` module.

`Langlands.GroupScheme.RelativeRoot.rootSubgroupUniqueness` proves exactly
`RootSubgroupUniquenessStatement.{u}` from
`Langlands.GroupScheme.Rational.RootSubgroupStructureStatement`. For every field
in any universe, a connected reductive group, a maximal split torus and a relative
root `a`, every smooth connected closed torus-stable subgroup whose ambient
tangent image is the full positive integral `a`-weight span has the same subgroup
functor as the constructed relative-root subgroup. The equality holds on every
test scheme. The group need not be split, and all positive integral multiples
are retained, including those present in nonreduced relative root systems.
The candidate subgroup's connectedness remains a hypothesis of the statement.

The helper `semigroupWeightSpan_cyclicTail_one_conjugation` is unconditional.
It uses the generic reindexing lemma `semigroupWeightSpan_cyclicTail`,
contributed by Worker 1302 in the paired `CyclicTailWeightSpan` module, and the
published `actionWeightSpace_conjugation` comparison. For a positive natural
number, the extra bound `1 ≤ n` in the first cyclic tail is automatic. Taking
the two indexed-supremum inequalities gives exactly `positiveWeightSpan i a`.
This helper permits every character, including zero, and does not require
splitness, smoothness or a relative-root hypothesis.

`rootSubgroupUniqueness_of_semigroup` records the assembly from
`SemigroupRealizationStatement.{u}` and
`CyclicRootFunctorComparisonStatement.{u}`. The given closed subgroup morphism
is a monomorphism of schemes, hence also a monomorphism over the base. Together
with its smoothness and connectedness, it witnesses
`IsSmoothConnectedClosed (SubgroupFunctor.range j)`. The weight-span equality
rewrites the given tangent image into the span for `cyclicTail a 1`. The final
uniqueness clause of `SemigroupRealizationStatement` then identifies the range
with that semigroup subgroup. The cyclic functor comparison identifies the
latter with the actual orbit-extension root functor. The maximal split torus
hypothesis supplies splitness, and membership in the relative roots supplies
the nonzero character needed by the cyclic comparison.

The final theorem discharges both premises with the published, unconditional
`semigroupRealization` and `cyclicRootFunctorComparison` proofs. Their modules
are imported directly. Thus neither realization nor cyclic comparison is an
additional premise of `rootSubgroupUniqueness`.

This is an internal composition of those proved results and the actual
all-test subgroup, action and character-lattice constructions. The source route
is Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second edition (2015),
Proposition 3.3.6, printed pages 109–110, followed by Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), section 2.6.8 and Proposition
2.11.9. The geometric arguments are implemented and explained in the imported
realization and cyclic-comparison modules; this module proves their
relative-root specialization without changing the published target.
