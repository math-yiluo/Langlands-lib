# Point fibres after restricting an atlas

This is an internal categorical construction from the published
`PseudofunctorPointFiber` and Mathlib's pseudofunctor coherence. It introduces
no new literature assertion.

Let `C` be a category, `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`, `i : V → U`,
`ξ ∈ F(U)` and `η ∈ F(T)`. Write `i*ξ` for ordinary pseudofunctor pullback.
All four object and morphism universe parameters remain arbitrary.

## The actual natural point map

For each `Z → T`, a point of the fibre of `i*ξ` and `η` is an actual map
`a : Z → V` together with an actual isomorphism `e : a*(i*ξ) ≅ p*η`,
where `p : Z → T` is its structure map.

`atlasComparison` is the composition comparison
`(a ≫ i)*ξ ≅ a*(i*ξ)`. `mapPoints` sends `(a, e)` to the actual point
`(a ≫ i, atlasComparison ≪≫ e)` of the original fibre. It retains the
isomorphism data and does not take isomorphism classes.

`atlasComparison_pullIso` uses associativity of the pseudofunctor composition
comparisons to prove compatibility with coherent pullback of isomorphisms.
`mapPoints_restrict` also identifies the base maps by associativity in `C`.
Consequently `presheafMap` is a natural transformation on the full slice
`Over T`, using every slice morphism.

## The equivalence under factorization

Assume `i` is a monomorphism. `mapPoints_injective` cancels `i` to identify
the actual maps to `V`, then cancels the composition-comparison isomorphism
to identify the original actual isomorphisms.

For any test `Z → T`, assume every original point `(b, e)` has a
factorization `a ≫ i = b`. No factorization is required for maps `b` that
do not underlie a point of this fibre. `mapPoints_surjective` uses such a
factorization and precomposes `e` with the inverse composition comparison
to construct a preimage.

`pointsEquiv` combines these two results. Its forward function is exactly
`mapPoints`, as recorded by `pointsEquiv_apply`. If the point-factorization
condition holds for every `Z → T`, `presheafIso` assembles the equivalences
into a natural isomorphism
`presheaf F (i*ξ) η ≅ presheaf F ξ η`. Naturality follows from the explicit
forward function and requires no separate compatibility assumptions on
chosen factorizations.

The factorization condition is an explicit hypothesis. This module constructs
neither a representing open nor an atlas. In the intended geometric
application, `i` will be the rank-one open of a coherent atlas family, and
the factorization condition must be proved for line-bundle test families.
The coherent-stack atlas, the actual Picard inclusion and its application
to the Picard-stack atlas remain separate obligations.
