# Permutation of embeddings and tensor coordinates

This internal algebraic unit defines the permutation of all `k`-algebra
homomorphisms `K → Ω` induced by an automorphism of `Ω` over `k`. The types
`k`, `K`, and `Ω` are arbitrary commutative semirings in independent
universes, with the two indicated `k`-algebra structures. Injectivity of
these homomorphisms and finiteness of their index are not assumed.

`embeddingPermutation k K Ω σ` sends `τ` to `σ ∘ τ`.
`embeddingPermutationHom` packages these permutations as a group
homomorphism, with `(σ * ρ)(x) = σ (ρ x)` as the multiplication convention.
`embeddingPermutationRepresentation` is the integer-linear permutation
representation on all functions from these homomorphisms to `ℤ`. Its
formula is `(σ m)(τ) = m(σ⁻¹ ∘ τ)`.

When the index has a `Fintype` instance, simultaneous transport of two
integer vectors preserves their dot product. The finite-product lemma
records the corresponding monomial formula: for any commutative group
and any family `a`, `∏ τ, a(σ ∘ τ) ^ m(τ)` equals
`∏ τ, a(τ) ^ (σ m)(τ)`. These are reindexing identities along the actual
embedding permutation.

`embeddingEvaluation_map_left` gives the semilinear transformation law
of the canonical tensor evaluation map: applying `σ` to the `Ω` tensor
factor evaluates at `τ` as `σ` of the original evaluation at
`σ⁻¹ ∘ τ`.

`tensorCoordinate φ τ` evaluates `K ⊗[k] R` in a commutative `k`-algebra
`R`, for an explicitly specified `k`-algebra map `φ : Ω → R`. It sends
`x ⊗ r` to `φ(τ(x)) * r`. Its coefficient-composition formula identifies
changing `φ` to `φ ∘ σ` with changing the index `τ` to `σ ∘ τ`.
`tensorCoordinate_natural` proves compatibility with every map
`ψ : R →ₐ[k] R'` and the map `id_K ⊗ ψ`.

These definitions and their short laws follow intrinsically from
composition of algebra homomorphisms, the tensor universal property,
and reindexing finite sums and products. They prepare the coefficient
calculation for Weil restriction. They do not assert a comparison with
the Galois action on any actual scheme's lattice, profinite continuity,
or existence of a finite-separable tensor decomposition.
