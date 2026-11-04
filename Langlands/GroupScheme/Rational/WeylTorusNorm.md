# The integral norm of the actual relative Weyl action on a torus

Author: Worker 1374.

This internal construction uses the actual rational normalizer and centralizer
of a map `i : T.toGrp ⟶ G` over a field `k : Type u`, where `T` is a
commutative group scheme. The underlying scheme map of `i` is monomorphic.
The definition `normalizerTorusAction` sends each actual normalizing point
to its uniquely determined automorphism of `T`. The multiplication order
agrees with `CategoryTheory.Aut`: the automorphism of `n * m` first applies
the automorphism of `m`, then that of `n`. Actual centralizer points act
trivially. Thus `relativeWeylTorusAction` descends to the actual quotient
`relativeWeylGroup i = N(k)/Z(k)`.

Postcomposition of an actual cocharacter with this torus action is the
published `relativeWeylCocharacterAction`. This identity follows on
normalizer representatives and hence on every quotient class. No
rational-point surjectivity of an algebraic quotient or isogeny is used.

For a finite actual quotient, `relativeWeylTorusNorm i : T ⟶ T` is the sum
of its actual automorphisms in the additive Hom group of commutative
group schemes. On each test scheme it takes the product of all Weyl
translates of a point. Its composite with any integral cocharacter is
exactly the published `relativeWeylCocharacterSum i`.

If the image of a point of `T` belongs to any normal subgroup functor `F`
of `G`, then so does the image of every Weyl translate, and hence the
image of its norm. The proof identifies translation by a normalizer
representative with actual ambient conjugation by its constant point on
the same test scheme. It then uses normality and subgroup closure under
finite products. This applies to the whole original torus point; it
requires no derived membership of separate coordinate cocharacter
factors.

The general helper `isCentral_of_forall_cocharacter` says that a map from
a split torus is central if all of its cocharacter composites are
central. The published finite character/cocharacter decomposition of the
identity writes every point, on every test scheme, as a finite product of
cocharacter values. The preimage of the full scheme-theoretic centre is
a subgroup, so it contains that product.

Finally, when `T` is split and `G` is affine, smooth and connected, the
published centrality theorem for integral Weyl sums proves that the norm
followed by `i` is central. This retains the explicit hypothesis that
every actual relative root has an actual relative reflection. Neither
maximality nor reductivity is assumed. The finite quotient instance,
splitness and reflection existence are premises; this module does not
prove them.

The provenance is internal: this is a direct combination of the published
normalizing-point laws, actual relative Weyl quotient and cocharacter
action, integral Weyl sums, split-torus identity decomposition and
centrality theorem. It introduces no additional literature assertion and
does not prove the full ambient smooth-real annihilation target.
