# Dimension of the tensor descent and the canonical Galois closure

This module continues `Langlands.Algebra.BrauerCorestriction.Construction`. It does two things:

1. It computes the dimensions of the conjugates `A^σ = N ⊗_{σ,L} A`, of their tensor product over `N`, and of the descended `K`-algebra `corAlg K L N A`.
2. It defines the canonical finite Galois closure used to define corestriction: the normal closure of `L/K` inside the separable closure of `K`.

No hypothesis on the characteristic or on infiniteness of `K` is used.

## Public declarations

Everything is in the namespace `Langlands.BrauerCorestriction`.

**Dimensions.** `A` is an `L`-algebra and `σ : L →ₐ[K] N`.

- `conj_finiteDimensional` (instance): if `A` is finite-dimensional over `L`, then `Conj A σ` is finite-dimensional over `N`.
- `finrank_conj`: `finrank N (Conj A σ) = finrank L A`.
- `finrank_conjTensor`: if `L/K` and `A/L` are finite, then `finrank N (ConjTensor K L N A) = (finrank L A) ^ Nat.card (L →ₐ[K] N)`.
- `finrank_corAlg_eq_pow`: if moreover `N/K` is finite Galois, then `finrank K (corAlg K L N A) = (finrank L A) ^ Nat.card (L →ₐ[K] N)`.
- `finrank_corAlg_of_card`: under the same hypotheses, if `N` admits exactly `[L : K]` embeddings of `L` (`Nat.card (L →ₐ[K] N) = finrank K L`), then `finrank K (corAlg K L N A) = (finrank L A) ^ [L : K]`.

**Canonical closure.** Let `SeparableClosure K` be Mathlib's separable closure of `K`, the separable closure of `K` in `AlgebraicClosure K`.

- `canonicalClosure K L : IntermediateField K (SeparableClosure K)` is Mathlib's `IntermediateField.normalClosure K L (SeparableClosure K)`: the compositum of the images of all `K`-embeddings `L → SeparableClosure K`. It needs no embedding of `L` as input, and it lies in the universe of `K`.
- `canonicalClosure_isGalois` (instance): it is Galois over `K`, for every extension `L/K`.
- `canonicalClosure_finiteDimensional` (instance): it is finite-dimensional over `K` when `L/K` is finite.
- `natCard_algHom_canonicalClosure`: for `L/K` finite separable, `Nat.card (L →ₐ[K] canonicalClosure K L) = [L : K]`. Hence the dimension formula of `finrank_corAlg_of_card` applies to the canonical closure.

## Implemented proof

**Conjugates.** `Conj A σ` is finite over `N` by `Module.Finite.trans` through `Twist σ`, over which it is a finite base change. For the dimension, the tower law `Module.finrank_mul_finrank` for `N → Twist σ → Conj A σ` and `Module.finrank_baseChange` give `finrank N (Twist σ) * finrank L A`. The first factor is `finrank N N = 1`.

**Tensor product.** Reindex a finite basis of each `Conj A σ` by `Fin (finrank L A)`, using `finrank_conj`. Mathlib's `Basis.piTensorProduct` gives a basis of `ConjTensor K L N A` indexed by the functions `(L →ₐ[K] N) → Fin (finrank L A)`. There are `(finrank L A) ^ #(L →ₐ[K] N)` such functions (`Fintype.card_pi`). The embeddings form a finite type because `L/K` is finite.

**Descended algebra.** The dimension of `corAlg` equals that of `ConjTensor` by `finrank_corAlg`, which comes from Galois descent.

**Canonical closure.** The separable closure is Galois over `K`, so `IntermediateField.normalClosure` inside it is normal (`normalClosure.normal`). It is separable because it embeds in a separable extension (`Algebra.IsSeparable.of_algHom`). Normal and separable give Galois (`isGalois_iff`). Finite dimensionality is `normalClosure.is_finiteDimensional`. `normalClosure.algHomEquiv` shows that every `K`-embedding into the separable closure factors through the normal closure. The minimal polynomial of each element of `L` is separable, so it splits in the separably closed field `SeparableClosure K` (`IsSepClosed.splits_codomain`). Then `AlgHom.natCard_of_splits` counts exactly `[L : K]` embeddings.

## Sources and scope

J. Tits, *Représentations linéaires irréductibles d'un groupe réductif sur un corps quelconque* (1971), §5.3, printed p. 208 / PDF p. 13, works over the separable closure `k_s` with representatives of `Γ/Γ₁`, which are `[k₁ : k]` in number. The canonical closure here is a finite Galois subextension of the separable closure containing all conjugates of `L`. It realizes the same index set of `[L : K]` embeddings, which `natCard_algHom_canonicalClosure` proves. The dimension formula `(dim_L A)^[L:K]` for the tensor product of conjugates is implicit in Tits' construction. The proofs are internal derivations from Mathlib's tensor-product bases, normal closures and separable closures.
