# Compatible root-datum isogenies compare intrinsic root functors

This internal derived comparison supports the root-subgroup part of Milne,
*Algebraic Groups* (2017), Proposition 23.5, printed pp.485–486.
It uses a supplied compatible root-datum isogeny, rather than constructing one.
The registered official 2017 errata snapshot has no correction to Proposition 23.5.

Reducedness implies that roots with equal positive integer multiples have equal
indices: linear dependence gives equality or opposite roots, and the root-coroot
pairing excludes the opposite case. Consequently a target root restricts into the
positive cyclic tail of the corresponding source root exactly at the supplied
index.

The published restricted-torus comparison expresses the intrinsic restricted root
functor as a semigroup subgroup of the full target-torus action. The two selecting
semigroups agree on all occurring adjoint weights: both exclude zero, and the
nonzero weights are the roots of the supplied root datum. The published ambient
weight-support congruence therefore identifies their all-test subgroup functors.

The resulting equality needs only smooth affine target geometry, split tori,
the target root-datum predicate, and the supplied compatible weight map. It
assumes neither an isogeny of group schemes nor reductivity of the source group.
The final lemma applies ordinary homomorphism functoriality of orbit extensions
to obtain containment in the corresponding target root functor on every scheme.
It makes no fppf surjectivity claim.

The module also proves that inclusion between two whole root functors of an
actual reduced root datum is equivalent to equality of their indices. This uses
the published exclusion of a root from another root functor when it is outside
that root's positive cyclic tail. The argument uses intrinsic tangent support,
so it does not assume an algebraically closed or perfect field.

`rootPointsEquivOfRootDatumIsogeny` packages this functor equality as an actual
multiplicative equivalence on the subgroup of points of every test scheme. Its
forward and inverse maps preserve the ambient point itself; the accompanying
coercion lemma records the forward map. It is induced by equality of the two
subgroups, so restriction along any test-scheme morphism commutes with it.
