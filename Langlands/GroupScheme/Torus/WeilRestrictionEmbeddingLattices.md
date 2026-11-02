# Embedding lattices of the Weil-restricted multiplicative group

Worker 207.

This internal adapter assumes commutative rings `k` and `K`, a field `Ω`,
`k`-algebra structures on `K` and `Ω`, finite projectivity of `K` over `k`,
a finite type of algebra homomorphisms `K →ₐ[k] Ω`, and an explicit proof
`h` that the canonical map `embeddingEvaluation k K Ω` is bijective. All
three rings lie in the same universe. Write `W_Ω` for the actual base
change to `Spec Ω` of `WeilGm.commGroupScheme (CommRingCat.of k) K`.

`embeddingCharacterEquiv` and `embeddingCocharacterEquiv` identify the
actual lattices `characterLattice W_Ω` and `cocharacterLattice W_Ω` with
the integer-valued functions on all algebra homomorphisms `K →ₐ[k] Ω`.
They use `decompositionCharacterEquiv` and `decompositionCocharacterEquiv`
for the canonical algebra decomposition `embeddingDecomposition h`.
The field assumption on `Ω` permits the existing split-torus lattice
classification. Neither `k` nor `K` is required to be a field here.

On every test scheme over `Spec Ω`, including nonreduced tests,
`embeddingCharacterEquiv_symm_points` evaluates a character vector `m`
as the monomial `∏ τ, a(τ) ^ m(τ)` in the actual embedding coordinates
`a = embeddingPointsEquiv h T x`. This product formula uses a `Fintype`
instance. `embeddingCocharacterEquiv_symm_points` sends a unit parameter
`s` to the coordinates `τ ↦ s ^ m(τ)`. The theorem
`embedding_latticePairing_eq_sum` identifies the actual pairing with
`∑ τ, m(τ) * n(τ)`, and `embedding_latticePairing_isPerfPair` proves
that it is perfect.

For every `σ : Ω ≃ₐ[k] Ω`, the equivalences intertwine the actual Galois
representations of `LatticeGalois` with
`embeddingPermutationRepresentation k K Ω`. Explicitly, the vector of
the transported character or cocharacter is

`(σ m)(τ) = m(σ⁻¹ ∘ τ)`.

These are the theorems `embeddingCharacterEquiv_galoisRepresentation`
and `embeddingCocharacterEquiv_galoisRepresentation`; their inverse
forms are also supplied. This is a comparison with the Galois action on
morphisms of the actual base-changed group scheme. It is not merely a
new abstract representation on an unrelated integer module.

The character proof uses the all-test formula
`embeddingPointsEquiv_descentPoint`: changing a test scheme's coefficient
structure by `Spec σ` replaces its coordinate at `τ` by the old coordinate
at `σ ∘ τ`. The point formula for transported characters therefore gives
a monomial in these permuted coordinates. Finite-product reindexing
turns this into the monomial with exponents `m(σ⁻¹ ∘ τ)`. Equality on all
tests gives equality of the actual characters.

For cocharacters, the point formula for Galois transport says that the
descent of the transported cocharacter value is the original cocharacter
at the same unit. The descent-coordinate identity, evaluated at
`σ⁻¹ ∘ τ`, then gives the required power in coordinate `τ`. Equality of
embedding coordinates and equality on all tests give equality of the
actual cocharacters. Finally,
`embedding_latticePairing_galoisRepresentation` deduces invariance of
the actual pairing from its dot-product formula and simultaneous
permutation of both vectors.

These constructions and their laws are intrinsic consequences of the
existing decomposition, tensor-coordinate descent and lattice-transport
APIs. The explicit bijectivity input remains a separate obligation;
this unit does not derive it from finite separability. It supplies an
algebraic automorphism-group action and its actual-group comparison,
with no claim about continuity, field-torus classification, or existence
of a splitting field.
