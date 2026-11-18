# Independence of the Galois closure

The tensor-descent algebra `corAlg K L N A` from `Construction` depends on an auxiliary finite Galois extension `N/K`. This module proves that, up to an actual `K`-algebra isomorphism, it does not depend on `N`. The comparison works for any finite Galois `N` that admits exactly `[L : K]` embeddings of `L`. Any such `N` is compared with the canonical closure from `Dimension`. The hypotheses are:

- `L/K` is finite separable;
- `A` is a finite-dimensional central simple `L`-algebra.

The characteristic is arbitrary, `K` need not be infinite, and the fields may lie in different universes.

## Public declarations

Everything is in the namespace `Langlands.BrauerCorestriction`.

**Conjugation along embeddings.** Fix a `K`-embedding `F : N →ₐ[K] N'` and embeddings `σ : L →ₐ[K] N`, `τ : L →ₐ[K] N'` with `F ∘ σ = τ`.

- `twistEmb F σ τ h : Twist σ →ₐ[L] Twist τ` is `F` regarded as an `L`-algebra map.
- `embMap A F σ τ h : Conj A σ →ₛₗ[F] Conj A τ` sends `x ⊗ a` to `F x ⊗ a` (`embMap_tmul`). It is semilinear over `F` and multiplicative (`embMap_one`, `embMap_mul`).
- `embMap_conjMap` and `conjMap_embMap` say that composing with the Galois conjugations of `Construction` gives the `embMap` of the composite embedding.
- `tprod_embMap_congr` says that pure tensors built from `embMap` depend only on the embedding and on the source-index function.

**Comparison along an embedding.** Fix `ι : N →ₐ[K] N'` and a bijection `e` of the embedding sets with `e σ = ι ∘ σ`.

- `apply_symm_emb` gives `ι ∘ e⁻¹(τ) = τ`.
- `compareMap A ι e he : ConjTensor K L N A →ₛₗ[ι] ConjTensor K L N' A` reindexes along `e` and then applies `embMap A ι` in each factor (`compareMap_tprod`). It is unital, multiplicative and `K`-linear (`compareMap_one`, `compareMap_mul`, `compareMap_smul`).
- `compareMap_actMap`: if `ι ∘ g = g' ∘ ι` for Galois automorphisms `g` of `N` and `g'` of `N'`, then the comparison map intertwines `actMap A g` and `actMap A g'`.
- `compareMap_mem_corAlg`: if every automorphism `g'` of `N'` has such a partner `g`, the comparison map sends fixed vectors to fixed vectors.
- `corAlgHom A ι e he hN : corAlg K L N A →ₐ[K] corAlg K L N' A` is the induced `K`-algebra homomorphism (`corAlgHom_apply`).
- `corAlgHom_bijective` and `corAlgEquivOfEmb` say that this homomorphism is an isomorphism of `K`-algebras. The extra hypotheses are: `L/K` finite, `A` finite-dimensional central simple, and `N`, `N'` finite Galois.

**Independence.**

- `exists_restrict`: if `N/K` is normal and `ι : N →ₐ[K] N'`, every `g'` in `Gal(N'/K)` has a restriction `g` in `Gal(N/K)` with `ι ∘ g = g' ∘ ι`.
- `bijective_comp_of_natCard`: when the two embedding sets have the same finite cardinality, composition with `ι` is a bijection between them.
- `nonempty_algHom_canonicalClosure`: for `L/K` finite separable, the canonical closure has a `K`-embedding into every normal `N/K` that admits some `K`-embedding of `L`.
- `nonempty_corAlgEquiv_canonical`: for every finite Galois `N/K` with `Nat.card (L →ₐ[K] N) = [L : K]`, the descended algebras over the canonical closure and over `N` are isomorphic `K`-algebras.
- `nonempty_corAlgEquiv`: the same holds for any two such `N` and `N'`.

## Implemented proof

`embMap` is `Algebra.TensorProduct.map` of `twistEmb` and the identity. Semilinearity, multiplicativity and the composition laws are proved by induction on tensors, exactly as for `conjMap`. `tprod_embMap_congr` is proved by substituting both equalities.

`compareMap` is `piTensorSemilinear ι` composed with Mathlib's `reindex` along `e`. It preserves `1` and products by `PiTensorSemilinear.reindex_one`, `reindex_mul`, `piTensorSemilinear_one` and `piTensorSemilinear_mul`. It is `K`-linear because `ι` commutes with the structure maps from `K`.

**Equivariance.** Induct over scaled pure tensors. The scalars agree by `ι (g r) = g' (ι r)`. On a pure tensor both sides become pure tensors of `embMap` factors by `conjMap_embMap` and `embMap_conjMap`: one side uses the embedding `g' ∘ ι` and the other `ι ∘ g`, and these are equal. The source-index functions `ρ ↦ e⁻¹(g'⁻¹ ρ)` and `ρ ↦ g⁻¹(e⁻¹ ρ)` agree after applying the injective `e`. This uses `ι ∘ g⁻¹ = g'⁻¹ ∘ ι` and `apply_symm_emb`. `tprod_embMap_congr` then identifies the two sides. Fixed vectors go to fixed vectors because each `g'` has a partner `g`.

**Bijectivity.** `corAlgHom` is a ring homomorphism out of the simple ring `corAlg K L N A` (`isSimpleRing_corAlg`). Its target is nontrivial, so it is injective (Mathlib's `IsSimpleRing.injective_ringHom_or_subsingleton_codomain`). Both algebras have dimension `(dim_L A) ^ #(embeddings)` (`finrank_corAlg_eq_pow`), and the bijection `e` makes the exponents equal. An injective linear map between spaces of equal finite dimension is surjective (`LinearMap.injective_iff_surjective_of_finrank_eq_finrank`).

**Restriction.** For `exists_restrict`, make `N'` an `N`-algebra through `ι` and use Mathlib's `AlgEquiv.restrictNormal` with `restrictNormal_commutes`. Composition with `ι` is injective because `ι` is injective. Equal finite cardinalities make it bijective (`Function.Injective.bijective_of_nat_card_le`).

**Canonical closure.** The canonical closure is `normalClosure K L (SeparableClosure K)`. There are `[L : K] > 0` embeddings `L → SeparableClosure K`, so Mathlib's instance `isNormalClosure_normalClosure` applies. `IsNormalClosure.lift` embeds the canonical closure into any field in which every minimal polynomial of an element of `L` splits. In a normal `N` with an embedding `σ₀ : L → N`, the minimal polynomial of `x` equals that of `σ₀ x` (`minpoly.algHom_eq`), and it splits by normality (`Normal.splits`).

For `N` with `[L : K]` embeddings, the cardinalities match those of the canonical closure (`natCard_algHom_canonicalClosure`). This gives the bijection `e` and the isomorphism `corAlgEquivOfEmb`. Two such `N` are compared through the canonical closure.

## Sources and scope

Tits, *Représentations linéaires irréductibles d'un groupe réductif sur un corps quelconque* (1971), §5.3, printed p. 208 / PDF p. 13, works over the separable closure `k_s` with chosen coset representatives `θ ∈ Θ`. He notes that the action on `E` is unique and that the resulting class is the corestriction (formula (1)). Changing the representatives or replacing `k_s` by a finite Galois subextension is not discussed there. This module supplies the independence of the auxiliary finite Galois closure, which a finite-level formalization needs, as an internal derivation. Indexing by all embeddings, as in `Construction`, removes the choice of representatives. The comparison here is an actual algebra isomorphism. Independence of the representative `A` within its Brauer class is a separate statement, proved with the Brauer-class map.
