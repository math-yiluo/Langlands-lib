# Bounded descent along finite faithfully flat affinoid maps

For a complete ultrametric nontrivially normed field `K` and presented
affinoid `K`-algebras `A`, `B` and `C`, take a finite Banach map
`f : A → B` whose underlying ring map is faithfully flat. The
proposition `FiniteFaithfullyFlatBoundedDescentStatement K` says that a
bounded `K`-algebra map `g : C → B` has a unique bounded factorization
through `f` whenever its two composites to the actual completed affinoid
self-pushout of `B` over `A` agree.

The proof `finiteFaithfullyFlatBoundedDescent` uses the published finite
tensor comparison to convert equality in the completed self-pushout
to equality of `b ⊗ 1` and `1 ⊗ b` in the ordinary tensor product.
Passing the second factor to the module quotient of `B` by the image of
`A` kills the term with `1` in that factor. Faithful flatness makes
tensoring the quotient by `1` injective. This puts `b` in the image
of `A`. The converse follows from the affinoid pushout equation.

The image is therefore the closed equalizer of two continuous linear
maps. The Banach inverse estimate for the injective map `f` on its
closed image bounds its algebraic inverse on that image. Composing this
inverse with `g` supplies a bounded lift. Injectivity of `f` proves
uniqueness.

## Provenance

The argument is internal. It combines the published finite Banach tensor
comparison with Mathlib's faithfully flat tensor injection and
closed-range estimate. This supplies bounded coefficient descent for a
single finite faithfully flat affinoid map. Arbitrary localized étale
Hom descent requires the additional geometric reduction to such covers.
