# Finite separable extensions of the completion come from `K`: the non-archimedean case

This module proves `HenselianFiniteEtale.exists_field_of_isUltrametricDist`. Let `K` be a non-archimedean nontrivially normed field that is separably closed in its completion `K̂`. Then every finite separable field extension `E/K̂` is `K̂ ⊗_K L` for some finite separable field extension `L/K`.

It is the non-archimedean field case of the essential surjectivity in `HenselianFiniteEtaleEquivalenceStatement` (Conrad, printed p.14).

## Proof

The norm on `K̂` is `HenselianIffSeparablyClosed.completionNormedField K`. It is non-archimedean because the naturals have the same norms in `K` and in `K̂`.

Let `Ω = AlgebraicClosure K̂`. It carries the spectral norm (`spectralNorm.normedField`, `spectralNorm.normedAlgebra`), and Krasner's lemma holds for `Ω/K̂` (`IsKrasner.of_completeSpace_of_normal`). The proof runs as follows.

1. Let `β'` be a primitive element of `E`, with minimal polynomial `h` of degree `n = [E : K̂]`. Let `ι : E → Ω` be a `K̂`-embedding and `β = ι β'`. Choose `r > 0` with `r ≤ ‖β - x‖` for every root `x ≠ β` of `h` in `Ω`.
2. Since `K` is dense in `K̂`, choose `a_k ∈ K` with `‖a_k - h_k‖ < δ` for `k < n`, where `δ = r^n / ((n + 1) · max(1, ‖β‖)^n)`. Put `g₀ = X^n + ∑_{k<n} a_k X^k ∈ K[X]`, which is monic of degree `n`.
3. Since `h(β) = 0`, `g₀(β) = ∑ (a_k - h_k) β^k`, so `‖g₀(β)‖ ≤ n δ max(1, ‖β‖)^n < r^n`. Moreover `g₀` splits in `Ω`, and `g₀(β)` is the product of `β - γ` over its `n` roots (`Splits.aeval_eq_prod_aroots_of_monic`). So some root `γ` satisfies `‖β - γ‖ < r`. Otherwise `Multiset.pow_card_le_prod` in `ℝ≥0` would give `‖g₀(β)‖ ≥ r^n`.
4. Krasner's lemma (`IsKrasner.krasner`) gives `β ∈ K̂(γ)`. The minimal polynomial of `γ` over `K̂` divides `g₀`, so `[K̂(γ) : K̂] ≤ n = [K̂(β) : K̂]`. Hence `K̂(β) = K̂(γ)`. So `γ = ι γ'` for some `γ' ∈ E`, and `γ` has degree `n` over `K̂`.
5. In `E`, `γ'` is a root of `g₀`. Its minimal polynomial over `K` has degree `n`: at most `n` because it divides `g₀`, and at least `n` because the minimal polynomial over `K̂` divides its image. That image is therefore the minimal polynomial over `K̂`, which is separable, so `γ'` is separable over `K`.
6. `L = K(γ')` is finite separable of degree `n = [E : K̂]`, and `L ⊆ E`. By `HenselianFiniteEtale.nonempty_algEquiv_of_algHom`, `K̂ ⊗_K L ≅ E`.
