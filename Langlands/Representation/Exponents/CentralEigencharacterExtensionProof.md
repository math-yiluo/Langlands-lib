# Proof of the extension of generalized eigencharacters of a central action

Author: Worker 828.

`Langlands.centralEigencharacterExtension` proves the published proposition
`Langlands.CentralEigencharacterExtensionStatement.{uG,uA,uB,uX}`. It
introduces the quantified data and applies the generic theorem
`Langlands.exists_eigencharacter_extension`, whose hypotheses are exactly
those of the statement.

## Declarations and proofs

`Langlands.eq_of_eigen_of_mem_genEigenspace`: if `T u = c • u` with `u ≠ 0`,
and `(T - μ • 1) ^ k` kills `u`, then `c = μ`. By induction,
`(T - μ • 1) ^ j u = (c - μ) ^ j • u`.

`Langlands.exists_eigencharacter_extension`: let `π` be an admissible
representation of a group `G` with a topology. Let `φ : A →* G` be a
continuous homomorphism with central image, from a commutative group `A`
with a topology in which multiplication is separately continuous. Let
`A'` be a monoid and `β : A' →* A`. Every generalized eigencharacter `χ` of `(π.comp φ).comp β`
extends to a character `ψ` of `A` with:

- open kernel,
- `ψ` a generalized eigencharacter of `π.comp φ`, and
- `ψ.comp β = χ`.

The proof never assumes the whole carrier finite-dimensional:

1. Take a nonzero vector `v` in the uniform-power character space of `χ` and
   an open subgroup `K` fixing it, which exists because `π` is smooth.
2. Let `W` be the intersection of that character space with the `K`-fixed
   vectors. `W` is finite-dimensional by admissibility and nonzero because it
   contains `v`.
3. `W` is stable under every `π (φ a)`. Stability of the character space is
   the published `map_mem_characterSpace_of_intertwiningMap`, applied to
   `π (φ a)`, which is an intertwiner because `φ a` is central. Stability of
   the fixed vectors also follows from centrality.
4. The restricted operators commute, so the published
   `EndomorphismBound.exists_common_eigenvector` gives a common eigenvector
   `w ∈ W`. The published `EndomorphismBound.exists_character_of_forall_eigen`
   turns its eigenvalues into a character `ψ`.
5. `ψ` is an eigencharacter, hence a generalized one
   (`isGeneralizedEigencharacter_of_eigenvector`). It is trivial on the open
   subgroup `φ⁻¹(K)`, because `w` is `K`-fixed, so its kernel is open. Since
   `w` also lies in the character space of `χ`, the previous lemma gives
   `ψ (β b) = χ b` for every `b`.

The extension comes from an actual common eigenvector inside a
finite-dimensional, admissible fixed space. No equivariant extension of a
functional is used.

## Scope

The module adds no hypothesis to the statement. It uses no irreducibility,
finite length or finite-dimensionality of the whole carrier. It was first
written as the spectral step of the proof of
`Langlands.GLInductionWeakJacquetBoundsStatement` (task
5c9a0e18-0039-4f00-81bc-e103757b5a3a).
