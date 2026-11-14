# Actual root parametrizations for factor-one root pullbacks

Let a finite homomorphism `φ : G → G'` between connected reductive groups
over an arbitrary field commute with a specified isogeny `t : T → T'` of
split maximal tori. Supply actual reduced root data `P` and `P'` for their
inclusions. The setup explicitly assumes affine ambient groups and a target
locally of finite type. If a source root `P.root r` is exactly the pullback
`t ≫ P'.root s`, then
`IsRootDatumOf.rootParametrizationOfExactPullback` chooses an actual standard
additive-line homomorphism `u : Ga → G` representing the source root subgroup
whose composite `u ≫ φ` represents the entire corresponding target root
subgroup. Both representations concern the intrinsic root subgroup functors
on every scheme test.

`RelativeRoot.exists_equivariant_rootParametrization` first constructs the
source parametrization for any actual root with no higher positive roots.
Natural single-weight vector coordinates on a closed representative give
an isomorphism with a standard vector group. Their differential and the
one-dimensional split root Lie space force its dimension to be one. The
inverse coordinate isomorphism followed by the closed inclusion gives the
desired representative. Its scalar conjugation law follows directly from
the single-weight coordinate law.

`VectorGroup.IsTorusEquivariant.of_torusPullback` descends an exact scalar
conjugation law through an actual isogeny of the specified tori. It pulls
back the torus morphism along an arbitrary target-torus point, uses the
surjective flat base change as an epimorphism, and applies the original law
to the lifted source-torus point. Scalar parameters and character values
pull back as global functions.

For the main constructor, the commuting square transports the source
conjugation law to the composite, and the exact character equation permits
the preceding descent. Its finite-map monicity then follows from
`HomImage.mono_of_noHigherRoots`: the actual schematic image is an additive
line, and the differential of its closed inclusion makes its weight an
actual target root. The characteristic-power image polynomial therefore has
degree one, by reducedness of the target datum. A monic equivariant additive
line of the target root character represents the whole target root subgroup
by the existing root-subgroup uniqueness theorem.

This is derived internal content from the natural weight-coordinate,
actual schematic-image, split root Lie-line and monic root-parametrization
constructions. Inseparable torus isogenies and nonreduced scheme tests are
retained; injectivity of the original finite map's differential is never
assumed. Finiteness of `φ` alone is sufficient once the torus isogeny and
exact root pullback are supplied. This focused result does not construct
the general root-datum isogeny or prove its full centrality and isomorphism
comparisons.
