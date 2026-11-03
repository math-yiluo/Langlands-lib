# Closure properties of actual semigroup subgroup functors

This internal unit proves consequences of the pointwise subgroup-closure
construction in `WeightSemigroup`. Its motivation is the generated-subgroup
step in CGP, *Pseudo-reductive Groups*, second edition, Proposition 3.3.6
(printed pp.109–110; PDF pp.135–136), but its proofs use only the published
construction and elementary subgroup closure. No source representation or
structural theorem is assumed or proved here.

`semigroupSubgroup_le_iff` gives the exact universal property: inclusion of
the generated functor in any subgroup functor is equivalent to inclusion of
each admissible generator. The forward direction composes generator inclusion;
the reverse uses minimality of subgroup closure at each test scheme.

`semigroupSubgroup_isStable` proves stability under the actual automorphic
action by subgroup-closure induction. For a generating point, its original
subgroup supplies action stability; products, inverses and the identity are
preserved by the action laws. Applying the inverse acting point gives
`act_mem_semigroupSubgroup_iff`. Every assertion concerns every test scheme,
including nonreduced tests.

`actionWeightSupport_mono` transports the very same nonzero tangent vector
along subgroup inclusion. With an explicit support bound on the generated
functor, `semigroupSubgroup_maximality_of_support` deduces the maximality
equivalence for smooth connected stable closed subgroups. This lemma does not
establish that support bound. `semigroupSubgroup_eq_of_maximal_generator`
identifies any admissible greatest generator with the pointwise closure by
two inclusions.

`semigroupWeightSpan_mono` uses the same selected weight space in the larger
indexed supremum. `semigroupSubgroupOrderHom` packages the previously published
monotonicity theorem as an order homomorphism, with its definitional evaluation
formula. The base field universe is arbitrary. These elementary results do
not assume smoothness or splitness beyond premises already present in an
admissible generator. They do not establish smooth closed representability,
exact Lie image, uniqueness from Lie image, unipotence or a finite Ga-series.
