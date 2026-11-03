# Ambient isomorphisms of Borel and minimal parabolic subgroups

Worker 1262. This internal categorical prerequisite transports the published
Borel, parabolic, and minimal rational parabolic predicates along an isomorphism
of the ambient group scheme over an arbitrary field. No reductivity,
splitness, perfectness, or characteristic assumption is used. All range
comparisons concern every test scheme, including non-affine schemes.

`SubgroupFunctor.transport e F` defines ambient transport of an arbitrary
subgroup functor: a point belongs precisely when its postcomposition with
`e.inv` belongs to the original functor. The pointwise subgroups are comaps,
and naturality follows from associativity. Transport by the inverse recovers
the original functor, and transport preserves inclusions. These facts construct
`SubgroupFunctor.ambientOrderIso e`, an actual order isomorphism between the
two types of subgroup functors.

`SubgroupFunctor.range_comp_mono` postcomposes a pointwise lift through the second
subgroup with the ambient homomorphism. Applying it to an ambient isomorphism
and its inverse proves `range_comp_iso_le_iff` and `range_comp_iso_eq_iff`.

The imported `IsBorelSubgroup.comp_iso` from `Absolute.BorelTransport` preserves the closed-subgroup condition by composing
with the ambient isomorphism. The source's smoothness, connectedness and
solvability are unchanged. To prove maximality, postcompose any proposed larger
Borel presentation with the inverse ambient isomorphism, and apply the original
maximality condition.

`IsParabolicSubgroup.comp_iso` preserves the source's smoothness and the closed
immersion, and postcomposes the given geometric Borel subgroup with the
base-changed ambient isomorphism. Its Borel property follows from the previous
lemma, and its factorization follows by functoriality of base change.

`IsMinimalParabolicSubgroup.comp_iso` pulls a smaller parabolic subgroup back
through the inverse ambient isomorphism, applies the original minimality, and
postcomposes the resulting all-test range equality. Each predicate also has a
`comp_iso_iff` theorem obtained by transport in both directions.

The provenance is internal: these are direct deductions from
`Absolute.Borel`, `Absolute.ParabolicTransport`, `Rational.MinimalParabolic`,
and the closed-subgroup composition lemmas in `Rational.SplitRankTransport`.
They add no geometric existence or conjugacy premise and prove neither generic
minimality nor the rational Bruhat decomposition. In particular, they apply to
inner automorphisms without requiring any separate rational-point surjectivity.
