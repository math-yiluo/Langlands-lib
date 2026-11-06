# Descent of local subgroup conditions

Author: Worker 1726.

This internal construction works with the actual point functor of a group
scheme over an arbitrary base scheme, uniformly in the universe `u`.
`IsZariskiLocal` says that membership in its subgroup on any test scheme is
detected on arbitrary Zariski open covers of that test scheme. Every
monomorphically represented subgroup has this property, by the previously
proved gluing of morphisms through a monomorphism.

For an open cover of the base and a subgroup functor on each corresponding
base change of the ambient group, `IsMatching` asks that all local membership
conditions agree under every comparison of relative tests over the base.
The pullback point adjunction expresses these comparisons directly.
`descentSubgroup` consists of the points satisfying every local condition
after every such restriction. Multiplication, inversion and arbitrary
restriction preserve these conditions, so this defines an actual subgroup
functor. Under `IsMatching`, its base change to each cover member is exactly
the prescribed local subgroup: the identity comparison proves one inclusion,
and the matching condition proves the other.

If the local subgroup functors have Zariski-local membership, so does the
descended subgroup. For each local test, pull back the test-scheme cover and
apply local membership detection there. Naturality of the point adjunction
identifies the resulting restrictions with the prescribed local conditions.
This proves the all-test descent and locality claims; effective closed scheme
representability and the relative-torus property require separate arguments.
