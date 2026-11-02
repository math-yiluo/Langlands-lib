# Restricting an actual smooth scheme atlas

This internal construction combines the fully faithful point-fibre comparison,
the comparison for an actual isomorphism of atlas objects, and the comparison
for a monomorphic restriction of the atlas base. It introduces no new
literature assertion.

Let `α : F → G` be a strong transformation of category-valued pseudofunctors
on schemes over `S`, fully faithful on every fibre. Let `ξ ∈ G(U)`, let
`i : V → U` be a monomorphism over `S`, and let `L ∈ F(V)`. The explicit
input `e` is an actual isomorphism `α(L) ≅ i*ξ`.

For a test `η ∈ F(T)`, assume every actual point of the ambient fibre of
`ξ` and `α(η)`, over every object `Z → T` in the full slice, has a base map
factoring through `i`. Only the existence of each factorization is assumed;
there is no chosen-factorization compatibility hypothesis.

`restrictedAtlasPointFiberIso` first applies the fully faithful comparison,
then changes `α(L)` into `i*ξ` using `e`, then applies the monomorphic atlas
restriction comparison. Whiskering with `T.iteratedSliceBackward.op` gives a
natural isomorphism on all schemes over `T.left`. Actual base maps and actual
isomorphisms are retained throughout.

`restrictedAtlasPointFiber_smoothSurjectiveRepresented` composes an ambient
Yoneda representation with the inverse of that isomorphism. Its witness is
the same scheme `P` over `T.left` with exactly the same smooth surjective
structure morphism. If the factorization input holds for every source test
object, `isSmoothSurjectivePresentation_of_restrictedAtlas` applies this to
every fibre of an ambient smooth surjective presentation.

Finally, `hasLocallyFiniteTypeSmoothSchemeAtlas_of_restrictedAtlas` uses the
explicit scheme `V` and family `L` as a source atlas, assuming also
`LocallyOfFiniteType V.hom`. The scheme universe `u` remains arbitrary.

All inclusion, isomorphism, factorization, ambient-presentation and local
finite-type inputs are explicit hypotheses. This module constructs none of
these geometric inputs and proves no unconditional atlas existence. In the
Picard application they must be supplied by the actual line-bundle inclusion,
the coherent family's rank-one open and an actual coherent-stack atlas.
