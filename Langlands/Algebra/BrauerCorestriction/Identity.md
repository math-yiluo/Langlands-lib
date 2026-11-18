# Corestriction along the identity extension

For `L = K`, the field `N` admits exactly one `K`-embedding `K → N`, the structure map. So the tensor product of conjugates has a single factor `N ⊗[K] A`, and the descended algebra is `A` itself. This module constructs the actual isomorphism `A ≃ₐ[K] corAlg K K N A` and concludes that corestriction along the identity extension is the identity of `BrauerGroup K`. There is no restriction on the characteristic, and `K` need not be infinite.

## Public declarations

Everything is in the namespace `Langlands.BrauerCorestriction`. Let `N/K` be a field extension and `A` a `K`-algebra.

- `idTensor K N A a` is the pure tensor `⨂_σ (1 ⊗ a)`, taken over the embeddings `σ : K →ₐ[K] N`. There is exactly one embedding.
- `one_tmul_smul` computes `1 ⊗ (k • a) = algebraMap K N k • (1 ⊗ a)` in each conjugate.
- `idEmbed K N A : A →ₐ[K] ConjTensor K K N A` is the `K`-algebra homomorphism `a ↦ idTensor K N A a` (`idEmbed_apply`).
- `idEmbed_mem_corAlg` says that its values are fixed by the Galois action.
- `idCorHom K N A : A →ₐ[K] corAlg K K N A` is `idEmbed` with codomain restricted to the descended algebra.
- `idCorHom_bijective` says that `idCorHom` is bijective when `N/K` is finite Galois and `A` is finite-dimensional and simple.
- `idCorEquiv K N A : A ≃ₐ[K] corAlg K K N A` is the resulting actual algebra isomorphism.
- `cor_self K : cor K K = id` says that corestriction along the identity extension `K/K` is the identity map of `BrauerGroup K`. Here `K/K` is viewed through Mathlib's structure `Algebra.id`.

## Implemented proof

The index type `K →ₐ[K] N` is a subsingleton (Mathlib's `AlgHom.subsingleton_id`), and its element is `Algebra.ofId K N`.

**The embedding.** `idEmbed` is built with `AlgHom.ofLinearMap`:

- *Additivity.* Mathlib's `subsingletonEquiv` sends the pure tensor `⨂ f` to `f σ₀` and is injective. After applying it, both sides become `1 ⊗ (a + b)`.
- *`K`-linearity.* By `one_tmul_smul`, each factor `1 ⊗ (k • a)` equals `algebraMap K N k • (1 ⊗ a)`. Here the scalar `k` crosses the tensor sign over the base field and `σ k = algebraMap K N k`. Mathlib's `MultilinearMap.map_smul_univ` pulls the scalar out of the one-factor pure tensor, with exponent `1`.
- *Unit and products.* `1` is the pure tensor of the units. Products follow from `tprod_mul_tprod` and `Algebra.TensorProduct.tmul_mul_tmul`.

**Fixed values.** `actMap g` sends `⨂ (1 ⊗ a)` to `⨂ (g 1 ⊗ a) = ⨂ (1 ⊗ a)` (`actMap_tprod`, `conjMap_tmul`, `map_one g`).

**Bijectivity.** `A` is simple and the descended algebra is nontrivial, so `idCorHom` is injective. Its target has dimension `(dim_K A)^1` by `finrank_corAlg_eq_pow`, since there is exactly one embedding (`Nat.card_of_subsingleton`). Equal finite dimensions give surjectivity.

**The Brauer map.** `cor_mk_eq_of_closure` from `BrauerClass` allows any finite Galois closure with `[K : K] = 1` embedding. Use `N = K`. This avoids comparing two algebra structures on the canonical closure of `K/K`, which coincide only up to definitional unfolding. So `cor K K ⟦A⟧ = ⟦corCSAOf K K K A⟧`. That class equals `⟦A⟧` because `idCorEquiv` is an isomorphism, and isomorphic algebras are Brauer equivalent.

## Sources and scope

The requirement that corestriction along the identity extension is the identity, under the actual field identification, is a normalization requested for this construction. J. Tits, *Représentations linéaires irréductibles d'un groupe réductif sur un corps quelconque* (1971), §5.3, printed p. 208 / PDF p. 13, with `k₁ = k`, has a single conjugate, and the fixed algebra is `D₁`. The argument here is an internal derivation from the actual tensor descent.
