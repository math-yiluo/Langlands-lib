# Homogeneous coordinates for actual linear vector actions

This internal construction uses the existing natural Lie-basis transition
and the comparison of a linear vector action with its actual differential.
No new literature assertion is introduced.

Let `V` be an affine group scheme over a field `k` in arbitrary universe
`u`, and let `e` be natural group equivalences from the points of `V` on
every test scheme to the additive group of `Fin d` tuples of global
functions. Let `v` be a finite basis of the actual base-field Lie kernel.

`vectorCoordinatesInBasis e he v T` changes `e T` by the linear
`basisTransition` evaluated at the canonical relative algebra
`((algΓ (CommRingCat.of k)).obj T).unop`. Its underlying ring is precisely
the ring of global functions of `T`. The inverse uses the inverse basis
transition. Linearity proves compatibility with the group laws.

`vectorCoordinatesInBasis_natural` proves naturality on every test scheme:
apply the coefficient-natural Lie-basis transition to the algebra map
induced by the test morphism, and use naturality of `e`.

`vectorAffineCoordinates_inBasis` identifies this construction on an
affine test `Spec A` with `basisTransition` evaluated directly at `A`.
The proof uses the existing relative affine-sections isomorphism, whose
underlying ring map is the usual `ΓSpecIso` map, and transition naturality.

For an actual action `b` of a commutative group scheme `S`, a supplied
`IsLinearVectorCoordinates b e` hypothesis, and a supplied
`HomogeneousLieBasis b (𝟙 S.toGrp)`, the theorem
`IsLinearVectorCoordinates.homogeneous_affine_action` proves the diagonal
formula on every commutative test `k`-algebra: the changed coordinate `i`
of `b.act s x` is the changed coordinate `i` of `x` multiplied by the
actual character value of `q.weight i` at `s`. It combines the proved
homogeneous differential formula with the proved equality between the
original linear action and its differential in the original coordinates.

The natural coordinate construction uses all test schemes. The diagonal
action theorem in this file is stated on affine tests. Passing its
formula to arbitrary test schemes, choosing the homogeneous basis from
a split-torus decomposition, identifying semigroup subgroup functors, and
proving the full ordered-product theorem remain further work. All results
here retain empty coordinate sets, zero and repeated weights, and
arbitrary field characteristic.
