# Fixed limits and the limit homomorphism for abstract automorphic actions

This derived supporting module extends `Dynamic.Action` using the published
affine-line geometry in `Dynamic.Uniqueness`. It works over an arbitrary base scheme S, for an
actual automorphic multiplicative-group action a on a group scheme G, and on
every scheme T over S. All declarations are in
`Langlands.GroupScheme.AutomorphicAction`.

`limit` chooses the zero value of an orbit extension of a point in the
parabolic functor. `hasLimit_limit` records its defining property. This choice
requires no separatedness. Every subsequent result assumes that G is separated
over S, so separated-target affine-line uniqueness makes the chosen limit unique.

`HasLimit.mem_centralizer` proves that every limit is fixed on all refinements.
For an extension e, consider two morphisms on `(T times Gm) times A1`: acting on
e by the universal Gm point, and composing e with the published affine-line
scaling map `AffineLine.scale`. They agree on the multiplicative-group open by
the action law and naturality. The published
`AffineLine.hom_ext_of_unitInclusion` makes them equal everywhere. Evaluation
at zero, using `AffineLine.lift_zeroSection_scale`, identifies the orbit of
e(0) with its constant orbit. The universal fixed-point criterion gives the
claim, including arbitrary nonaffine and nonreduced tests.

`limit_eq` identifies the chosen limit with any specified limit, and
`limit_mem_centralizer` applies the fixed-limit theorem to the chosen one.
`limitHom` packages the choice as a homomorphism from parabolic to fixed points:
the product of orbit extensions has the product of their zero values, so
uniqueness supplies multiplicativity. `hasLimit_iff_limitHom` characterizes its
value, and `limitHom_comp` proves naturality under every test morphism. Constant
extensions show that fixed-point inclusion is a section, so the homomorphism is
surjective. `ker_limitHom` identifies its kernel with the identity-limit subgroup
inside the parabolic point group. Finally, `mul_inv_limit_mem_unipotent` uses a
constant extension of the fixed limit and its inverse to divide any parabolic
point into an identity-limit point and its fixed limit.

The proof adapts the published conjugation results in `Dynamic.Uniqueness` and
`Dynamic.LimitMap` to the actual abstract action. Its mathematical inputs are
those existing affine-line constructions, separated-target extension uniqueness,
and action laws; it invokes no additional external theorem. This unit asserts
no geometric realization, smoothness, Lie-weight comparison, or cyclic-tail
comparison.
