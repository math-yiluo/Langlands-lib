# The tensor descent of conjugate algebras

Let `K` be a field, `L/K` a field extension, `N/K` a field extension, and `A` an `L`-algebra (a possibly noncommutative ring). The four types have independent universes. This module constructs Tits' tensor descent of the conjugates of `A`:

1. For each `K`-embedding `σ : L →ₐ[K] N`, the conjugate `A^σ = N ⊗_{σ,L} A`, an `N`-algebra.
2. The tensor product `⨂_N σ, A^σ` over all `K`-embeddings `σ`.
3. The action of `Gal(N/K) = N ≃ₐ[K] N` on this tensor product by semilinear ring automorphisms that permute the factors.
4. The fixed `K`-subalgebra `corAlg K L N A`.
5. When `N/K` is finite Galois, the descent isomorphism `N ⊗[K] corAlg K L N A ≃ₐ[N] ⨂_N σ, A^σ`.

No hypothesis on the characteristic, on infiniteness of `K`, or on `A` is used here. Central simplicity of the fixed algebra, the choice of `N`, the Brauer class and its independence are treated in separate modules. In particular this module makes no claim about Brauer classes. Without further hypotheses on `N`, the set of embeddings may be smaller than `[L : K]`.

## Public declarations

Everything is in the namespace `Langlands.BrauerCorestriction`.

**Twisted copies of `N`.**

- `Twist σ` is a type synonym for `N` with its field structure. It is an `N`-algebra through the identity and a `K`-algebra through `N`. It is an `L`-algebra through the embedding `σ`, so `algebraMap L (Twist σ) l = σ l` (`algebraMap_L_apply`). The instances record the scalar towers `K → N → Twist σ` and `K → L → Twist σ`, the commutation of the `L`-action with the `N`- and `K`-actions, and finiteness over `N`. The synonym exists so that each embedding `σ` carries its own `L`-algebra structure on the same field `N`.
- `twistHom g σ τ h : Twist σ →ₐ[L] Twist τ` is the Galois automorphism `g` viewed as an `L`-algebra map, given a proof `h : ∀ l, g (σ l) = τ l` (`twistHom_apply`).

**Conjugate algebras.**

- `Conj A σ` is `Twist σ ⊗[L] A`, the conjugate `A^σ`. It is an `N`-algebra and a `K`-algebra through the left factor.
- `conjMap A g σ τ h : Conj A σ →ₛₗ[g] Conj A τ` sends `x ⊗ a` to `g x ⊗ a` (`conjMap_tmul`). It is semilinear over `g` and is defined for any `σ, τ` with `g ∘ σ = τ`. The proof `h` is an argument, so no cast along an equality of embeddings is needed. `conjMap_one_apply` says that `g = 1` gives the identity. `conjMap_conjMap` says that the maps compose to the map of `g * g'`. `conjMap_one` and `conjMap_mul` say that `conjMap` is multiplicative.

**The Galois action.**

- `ConjTensor K L N A` is `⨂[N] σ : (L →ₐ[K] N), Conj A σ`.
- `galPerm g` is the permutation `σ ↦ g ∘ σ` of the embeddings, with inverse `σ ↦ g⁻¹ ∘ σ` (`galPerm_apply_apply`, `galPerm_symm_apply_apply`, `apply_galPerm_symm`).
- `actMap A g` is a `g`-semilinear endomorphism of `ConjTensor K L N A`. It is Mathlib's reindexing along `galPerm g` followed by `piTensorSemilinear g` of the maps `conjMap A g (g⁻¹ τ) τ` (from `Langlands.Algebra.BrauerCorestriction.PiTensorSemilinear`). On pure tensors (`actMap_tprod`) it sends `⨂_σ x_σ` to `⨂_τ conjMap g (x_{g⁻¹τ})`: the factor at `σ` goes to the factor at `gσ` by `x ⊗ a ↦ g x ⊗ a`. `tprod_conjMap_congr` says that such a pure tensor depends only on the function `τ ↦ source index`, not on the compatibility proofs.
- `actMap_one_apply` and `actMap_mul_apply` are the group-action laws. `actMap_one` and `actMap_mul` say that each `actMap A g` is a ring endomorphism.
- `galAction K L N A : GaloisDescent.SemilinearAlgAction K N (ConjTensor K L N A)` packages these laws as a semilinear action by ring automorphisms (`galAction_act`). The structure is from `Langlands.Algebra.BrauerCorestriction.GaloisDescent`.

**The fixed algebra and descent.**

- `corAlg K L N A : Subalgebra K (ConjTensor K L N A)` is the fixed subalgebra of `galAction`, with membership given by `mem_corAlg`. This is the actual tensor-descent algebra.
- For `[FiniteDimensional K N] [IsGalois K N]`, `corAlgEquiv K L N A : N ⊗[K] corAlg K L N A ≃ₐ[N] ConjTensor K L N A` is the actual `N`-algebra isomorphism `x ⊗ a ↦ x • a` (`corAlgEquiv_tmul`) recovering the tensor product of conjugates after scalar extension. This is effective descent. `finrank_corAlg` gives `finrank K (corAlg K L N A) = finrank N (ConjTensor K L N A)`.

## Implemented proof

The `Twist` instances are transported from `N` by `inferInstanceAs`. The `L`-algebra structure is `RingHom.toAlgebra σ`. The tower `K → L → Twist σ` is `σ.commutes`, and the commutation instances are `mul_left_comm` in the field `N`.

`conjMap` is the underlying map of `Algebra.TensorProduct.map (twistHom g σ τ h) (AlgHom.id L A)`. Semilinearity is proved by induction on tensors: on `x ⊗ a`, the scalar `n` moves to the left factor (`smul_tmul'`) and `g (n x) = g n * g x`. The identity and composition lemmas are inductions on tensors; on pure tensors they hold by definition. Multiplicativity is inherited from `Algebra.TensorProduct.map`.

On pure tensors `actMap` is computed with `reindex_tprod` and `piTensorSemilinear_tprod`. For the action laws, induct over scaled pure tensors, using semilinearity to move the scalar out.

- **Identity.** For `g = 1`, the source-index function `τ ↦ 1⁻¹ ∘ τ` equals `τ ↦ τ`. `tprod_conjMap_congr`, proved by `subst`, replaces one by the other. Then `conjMap_one_apply` removes each conjugation.
- **Composition.** For `g * g'`, `actMap g (actMap g' (⨂ x))` is a pure tensor whose factors are `conjMap g (conjMap g' (x_{g'⁻¹ g⁻¹ τ}))`. `conjMap_conjMap` turns each factor into `conjMap (g g')`. The source-index functions `τ ↦ (g g')⁻¹ ∘ τ` and `τ ↦ g'⁻¹ ∘ (g⁻¹ ∘ τ)` agree by injectivity of `g g'`, and `tprod_conjMap_congr` identifies the two pure tensors.

Multiplicativity of `actMap` combines `PiTensorSemilinear.reindex_mul` and `reindex_one` with `piTensorSemilinear_mul` and `piTensorSemilinear_one` for the multiplicative maps `conjMap`. The fixed algebra, the descent isomorphism and the dimension formula are the corresponding results of `GaloisDescent` (`fixedSubalgebra`, `descentAlgEquiv`, `finrank_fixedSubalgebra`) applied to `galAction`.

## Sources and scope

The construction is J. Tits, *Représentations linéaires irréductibles d'un groupe réductif sur un corps quelconque* (1971), §5.3, printed p. 208 / PDF p. 13. Tits takes a finite separable extension `k₁/k` with `k` infinite and a central division `k₁`-algebra `D₁`. He chooses representatives `θ ∈ Θ` of `Γ/Γ₁` in the absolute Galois group `Γ` and forms the conjugates `D_θ` and `E = ⊗_{k_s} (D_θ ⊗_{k_θ} k_s)`. `Γ` acts on `E` inducing the natural action on `k_s`, with `Γ₁` acting trivially on `D₁` and `θ` acting on `D₁` through `θ`. The corestriction representative is the fixed algebra of `E`. The remark on printed p. 209 / PDF p. 14 allows this formula to be taken as the definition of corestriction.

This formalization differs from that presentation in three ways:

- It works over a finite Galois extension `N/K` instead of the separable closure. Effective descent for a finite Galois group is `GaloisDescent`.
- It indexes the factors by all `K`-embeddings `σ : L → N` instead of chosen coset representatives. When `N` contains a normal closure of `L/K`, these embeddings are in bijection with `Γ/Γ₁`, so no choice of representatives is involved.
- It accepts an arbitrary `L`-algebra `A`. Central simplicity and the Brauer class are treated in later modules.

The action agrees with Tits': `g` sends the conjugate at `σ` to the conjugate at `gσ` by `x ⊗ a ↦ g x ⊗ a`. In particular, the stabilizer of an embedding fixes the elements `1 ⊗ a` of that factor. Tits' infiniteness assumption on `k` is not used here.
