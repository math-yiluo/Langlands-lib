# Minimal finite free covers over a local ring

This internal construction supports the comparison argument for the residue-field
projective-dimension lower bound. It uses the local-ring module and Nakayama
interfaces in the pinned Mathlib. It does not assert the lower bound itself.

For a commutative local ring `R` and an `R`-module `M`,
`MinimalFiniteFreeCover R M` records a natural number `rank`, a surjective linear
map from `Fin rank →₀ R` to `M`, and containment of its kernel in the product of
the maximal ideal with the whole source module.

`nonempty_minimalFiniteFreeCover` proves existence when `M` is finitely generated,
without a Noetherian assumption. The proof chooses a basis of
`ResidueField R ⊗[R] M`, lifts its basis vectors to `M`, and uses Nakayama to show
the lifts span `M`. The resulting free cover is a bijection after extension of
scalars to the residue field: it is surjective and its source and target have
the same finite dimension. Injectivity after tensoring shows that every vector
in its kernel is zero modulo the maximal ideal.

`minimalFiniteFreeCover` chooses one such cover by classical choice.
