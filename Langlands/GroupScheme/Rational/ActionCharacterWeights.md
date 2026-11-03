# Intrinsic weights of actions descended through a character

This internal supporting module works over every field `k : Type u` with
an affine group scheme `G` locally of finite type. All weights are the
intrinsic differential weights of an actual automorphic action.

For split acting tori, `actionWeightSpace_restrict_eq_of_injective` says
that restriction preserves each weight space exactly when restriction
on characters is injective. The grouped-weight formula from
`ActionCocharacterWeights` has only one possibly contributing original
character in this case. `actionWeightSpaceRestrictEquiv` packages the
result as a linear equivalence whose underlying vector is unchanged.

Let `a` be any nonzero character of a split torus `S`, and let `e` be an
actual multiplicative-group action on `G`.
`actionWeightSpace_restrict_character` identifies the `n • a` weight
of the restricted action with the `n`-th power weight of `e`, for every
natural `n`, including zero. The published `characterFpqc` theorem
makes the underlying character map flat and surjective. This map is
an epimorphism of schemes, so cancellation gives injectivity of
restriction on characters. The generic exact restriction theorem then
applies. The proof does not assume that `a` is primitive or that its
kernel is smooth.

`semigroupWeightSpan_restrict_character_cyclicTail` reindexes the
positive multiples in the first cyclic tail and identifies their span
with `e.positiveWeightSpan`. Its corollary
`positiveWeightSpan_eq_top_of_restrict_character` gives full strictly
positive Lie span from full cyclic span of the restricted action.
No hypothesis on connectedness or smoothness of `G` is required.

The provenance is internal, from the grouped intrinsic weight formula,
the published actual fpqc character theorem, cancellation for scheme
epimorphisms, and elementary reindexing of positive natural integers.
No descent construction, subgroup containment, representability, or
cyclic-root comparison is asserted by this module.
