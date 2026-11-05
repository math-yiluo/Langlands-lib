# Non-local-compactness of the adelic affine-line subspace

This is the non-local-compactness assertion in Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (2011), printed p.10, Example 4.3.
The original adelic coefficient carrier is given the independently defined
subspace topology from the unrestricted product of completed fields. This space
is not locally compact. The range of the actual standard affine-line point map
`a ↦ [1:a]` in actual adelic projective one-space, with the subtype topology from
its arithmetic model topology, is likewise not locally compact.

The first conjunct refers to the original restricted-product coefficient
carrier with the product-induced topology. The second uses the literal range
of `projectiveLineAffinePoint`, an actual relative scheme point constructed
through the polynomial-Proj affine chart. Its ambient topology comes from the
concrete arithmetic projective model and its canonical generic-fiber
identification, independently of the affine inclusion. This therefore asserts
failure of local compactness of the actual projective subspace.

Both global-field characteristics are included in an arbitrary common universe.
The function-field branch permits any finite extension of the chosen
rational-function field over finite constants, including inseparable ones.
The number-field branch retains all infinite and finite completion factors.
Every finite initial arithmetic set is allowed; allowing the empty initial
curve set uses the cofinal system of larger nonempty stages, as for the
published affine-line subspace comparison.

This file defines propositions, not their proofs. Neither infinitude of an
abstract place set nor noncompactness of supplied local spaces is assumed.
The ordinary adelic topology and the affine-line subspace topology are distinct
constructions; the assertion here concerns the latter. Rational-point density,
nonclosedness and nondiscreteness of projective rational points remain separate
assertions of Example 4.3.
