# Effective étale descent of affine group schemes over an arbitrary base

This internal construction combines `LocalSolutionEffectivity` and
`EtaleAffineBaseEffectivity`. It is derived from the actual scheme and group
constructions in those modules, with no additional literature claim.

Work in any universe `u`. Let `p : S → B` be a surjective étale morphism of
schemes, let `G` be an actual group scheme over `S` whose structure morphism
is affine, and let `D : Descent.Datum p G` be an actual Čech descent datum.
`Datum.etaleSolution` constructs a `Solution D`. Its group scheme is affine
over `B`, as proved by `Datum.etaleSolution_isAffineHom`. Neither `B` nor `S`
is required to be affine, and no quasi-compactness hypothesis on `p` is used.
There are no smoothness, finite type, reductivity, or commutativity premises.

The preliminary instance `LocalSolutionGluing.obj_isAffineHom` works for
supplied solutions on any small thin locally directed open cover of `B`.
If each local solution has affine structure morphism, the glued quotient
also has affine structure morphism. Affineness is local on the target. For
each chart, the relative gluing construction identifies the canonical
pullback of the global structure map with the supplied local structure map.
The inverse pullback comparison expresses that canonical projection as an
isomorphism followed by the local affine morphism. Closure under composition
and locality prove the claim.
`LocalSolutionGluing.solution_isAffineHom` uses the fact that reconstruction
of the group operations preserves this underlying scheme over `B`.

For unconditional existence, use `B.directedAffineCover`, the small thin
locally directed cover of all affine open subschemes of `B`. Pulling `D`
back to a chart preserves étaleness and surjectivity of the covering map and
affineness of the original group's structure map. The constructor
`Datum.etaleAffineBaseSolution` therefore gives an actual local solution
with affine total space on each affine chart. Its structure morphism is
affine because both source and target are affine.
`LocalSolutionGluing.solution` glues these local solutions to a solution of
the original unchanged datum. The preceding locality argument proves the
affineness of its structure morphism.

The output includes an actual group scheme over `B`, an isomorphism from
its pullback to the given group scheme over `S`, and compatibility with the
specified descent datum. This unit supplies effective descent; the host
quasi-split inner-form theorem also requires separate geometric and inner
discrepancy constructions.
