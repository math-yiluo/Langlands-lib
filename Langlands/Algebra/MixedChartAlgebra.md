# Universal finite-character Hopf points and twists

For a finitely presented commutative Hopf algebra `A` over a
commutative ring `R` and a finite additive commutative group `L`,
`Langlands.Algebra.MixedChartAlgebra.W R A L` is the published
`HomAlgebra R A R[L]`. The module expresses its universal Hopf point
in group-algebra coordinates as `univ : A →ₐ[R] W[L]` and constructs
`pointOf g` by pushing this point along a coefficient map
`g : W →ₐ[R] C`.

The auxiliary lemmas prove the Hopf-point equations, identify
`pointOf` with the published representing equivalence for coefficient
rings in the same universe, and compare point evaluation with the
character-endomorphism twist of the universal algebra. Maps into
coefficient rings in other universes are handled directly by the
universal-point formula where the Lean statement allows them.

`twist_injective_of_surjective` proves freeness of these twists at
surjective scalar-extended points over a nonzero coefficient ring:
if two character automorphisms give equal twisted Hopf points, they
are equal. Apply the inverse of one automorphism and cancel the
surjective scalar-extended map; the resulting character automorphism
must be the identity.

This is an internal construction adapted from the published torus
chart algebra, but with an arbitrary finite additive commutative
character group. It uses the existing finite-bialgebra Hom algebra,
group-algebra comparison and twisting APIs. It asserts no smoothness
of `W`, no quotient scheme and no subgroup-chart existence.
