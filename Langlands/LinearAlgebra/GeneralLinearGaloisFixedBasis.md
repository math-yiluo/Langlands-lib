# Galois-fixed bases for `GL_n`-valued cocycles

This module proves Hilbert's Theorem 90 for `GL_n` over a finite field
extension `L/K`, in the following matrix form.

**`exists_fixed`.** Let `g : (L ≃ₐ[K] L) → GL n L` satisfy the cocycle
identity `g (σ * τ) = g σ * σ(g τ)`, where `σ(-)` applies `σ` to every
matrix entry (`GeneralLinearGroup.map (σ : L →+* L)`). Then some
`P : GL n L` satisfies `g σ * σ(P) = P` for every automorphism `σ`.

Finiteness of `L/K` is used only to make the automorphism group finite.
`IsGalois` is not assumed. The index type `n` is any finite type with
decidable equality.

## Proof

- `linearIndependent_automorphisms` is Dedekind's lemma: the automorphisms
  of `L` over `K` are `L`-linearly independent as functions `L → L`. It
  restricts Mathlib's `linearIndependent_monoidHom` along the injective map
  from automorphisms to monoid homomorphisms, as in Mathlib's proof of
  Hilbert 90 for `Lˣ`.
- `cocycle_one`: a cocycle satisfies `g 1 = 1`, because `g 1 = g 1 * g 1`.
- `average g v` is the twisted average `Σ_τ g_τ τ(v)` of a vector
  `v ∈ Lⁿ`. `average_fixed` shows that it is fixed by the twisted action
  `w ↦ g_σ σ(w)`. Applying `σ` gives `Σ_τ σ(g_τ) (στ)(v)`; multiplying by
  `g_σ` gives `Σ_τ g_{στ} (στ)(v)` by the cocycle identity, and
  reindexing by `τ ↦ στ` returns the average.
- `dual_eq_zero`: an `L`-linear functional `f` that vanishes on every
  twisted average is zero. Fix a standard basis vector `eᵢ` and put
  `c_τ = f(g_τ eᵢ)`. For `l ∈ L` the average of `l eᵢ` is
  `Σ_τ τ(l) g_τ eᵢ`, so `Σ_τ c_τ τ(l) = 0` for all `l`. By Dedekind's lemma
  every `c_τ` vanishes. The case `τ = 1`, with `g 1 = 1`, gives
  `f(eᵢ) = 0`.
- `span_range_average`: the twisted averages span `Lⁿ`. Otherwise
  Mathlib's `Submodule.exists_dual_map_eq_bot_of_lt_top` gives a nonzero
  functional vanishing on their span, contradicting `dual_eq_zero`.
  Projectivity of the quotient holds because every module over a field is
  free.
- `exists_fixed`: Mathlib's `Basis.ofSpan` extracts a basis of `Lⁿ`
  consisting of twisted averages, reindexed by `n` with
  `Basis.indexEquiv`. Let `P` be the matrix whose columns are these basis
  vectors, `(Pi.basisFun L n).toMatrix b`. Its inverse is
  `b.toMatrix (Pi.basisFun L n)`. Column `j` of `g_σ σ(P)` is
  `g_σ σ(b_j) = b_j`, so `g_σ σ(P) = P`.

## Source

Knus, Merkurjev, Rost and Tignol, *The Book of Involutions* (1998),
registered as `knus-merkurjev-rost-tignol-1998-book-of-involutions`.
Theorem 29.2 (Hilbert's Theorem 90), printed p.392 / PDF p.415, states
`H¹(F, GL₁(A)) = 1` for every separable associative algebra `A`. The case
`A = M_n(F)` is the vanishing of `H¹(F, GL_n)`. The module proves the
finite-level form of that case directly, for cocycles of the finite
automorphism group of `L/K`. The proof route through twisted averages and
Dedekind's lemma is derived; the cited proof instead uses a descent
isomorphism for modules.
