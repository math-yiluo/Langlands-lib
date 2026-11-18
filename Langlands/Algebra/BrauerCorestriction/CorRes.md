# The tensor descent of a scalar extension

Let `B` be a finite-dimensional central simple `K`-algebra, `L/K` finite and `N/K` finite Galois, with `K`, `L`, `N` and `B` in one universe. Write `E = L →ₐ[K] N` and `C = ⨂_K (σ : E), B`. This module proves that the descended algebra of the scalar extension `L ⊗_K B` satisfies

`corAlg K L N (L ⊗_K B) ⊗_K Cᵐᵒᵖ ≃ₐ[K] M_r(K)`,

with an actual algebra isomorphism `corResSplitEquiv`. Here `r = (dim_K B)^|E|`. The isomorphism holds for every such `N`, including fields `N` into which `L` has fewer than `[L : K]` embeddings or none at all (then `E` is empty, `C = K` and `r = 1`).

**Brauer-class interpretation.** The algebra `corAlg K L N (L ⊗_K B)` represents the corestriction of the restriction of `[B]` only under the full-embedding condition: `L/K` is finite separable and `Nat.card (L →ₐ[K] N) = finrank K L`, as in `cor_mk_eq_of_closure` of `BrauerClass`. Under this condition, `corResSplitEquiv` makes `corAlg K L N (L ⊗_K B)` Brauer equivalent to `C`, whose class is `|E| · [B] = [L : K] · [B]`. For every finite separable `L/K` the canonical closure `canonicalClosure K L` of `Dimension` satisfies the condition (`natCard_algHom_canonicalClosure`). This module states no Brauer-class result. The class statement `Cor(Res x) = [L : K] • x`, with the degree formula, is proved in `CorResClass` with the canonical closure. Without the condition the fixed algebra need not be the corestriction. For example, take `K = N = ℚ` and `L = ℚ(∛2)`. Then `E` is empty and `corAlg` is `ℚ`, but `Cor(Res[B]) = 3[B]`.

The proof uses no group law on Brauer classes and no hypothesis on the characteristic.

## Public declarations

Everything is in the namespace `Langlands.BrauerCorestriction`.

**Embedding `C` into the tensor product of conjugates.**

- `baseFactor K L N B σ : B →ₛₗ[algebraMap K N] Conj (L ⊗_K B) σ` is `b ↦ 1 ⊗ (1 ⊗ b)` (`baseFactor_apply`). It is unital and multiplicative (`baseFactor_one`, `baseFactor_mul`).
- `baseEmbed K L N B : C →ₐ[K] ConjTensor K L N (L ⊗_K B)` is the induced `K`-algebra map (`baseEmbed_tprod`).
- `actMap_smul_base` says that the Galois action is `K`-linear.
- `actMap_baseEmbed`: on the image of `C`, the Galois action of `Construction` is the permutation of tensor factors along `galPerm g`.

**The twisted action.**

- `galPermHom K L N : Gal(N/K) →* Equiv.Perm E` is `g ↦ (σ ↦ g ∘ σ)`.
- `twistUnit K L N B g` is the permutation unit `permUnits K B E (galPermHom g)` of `PermUnits`. `twistUnit_conj` says that it implements `galPerm g` on `C`.
- `twistAct K L N B g` is the additive map `t ↦ g(t) · j(w_g)`, where `j = baseEmbed` and `w_g = twistUnit g` (`twistAct_apply`).
- `twistedAction K L N B` packages these maps as a semilinear Galois action (`twistedAction_act`).
- `twistFixed K L N B` is its fixed `K`-subspace, with membership `mem_twistFixed`.
- `mul_mem_twistFixed`: left multiplication by the descended algebra `corAlg K L N (L ⊗ B)` preserves the fixed space.
- `mul_baseEmbed_mem_twistFixed`: right multiplication by `j(c)` preserves it.
- `conjTensor_mul_smul` and `conjTensor_smul_mul` record compatibility of `K`-scalars with multiplication.

**The bimodule isomorphism.**

- `leftAct K L N B : corAlg →ₐ[K] End_K(fixed)` is left multiplication.
- `rightAct K L N B : Cᵐᵒᵖ →ₐ[K] End_K(fixed)` is right multiplication through `j`.
- `bimoduleAct K L N B` combines them into a homomorphism from the tensor product. The two actions commute by associativity.
- `finrank_twistFixed` and `finrank_twistFixed_pos` give `dim_K(fixed) = (dim_K B)^|E| > 0`.
- `bimoduleMatrix K L N B` writes `bimoduleAct` in a basis of the fixed space.
- `bimoduleMatrix_bijective` and `corResSplitEquiv K L N B` give the isomorphism `corAlg K L N (L ⊗_K B) ⊗_K Cᵐᵒᵖ ≃ₐ[K] M_r(K)`.

## Implemented proof

**The embedding.** Each factor map is semilinear over `K → N`. A scalar `k` moves through `1 ⊗ (1 ⊗ k b) = σ(k) ⊗ (1 ⊗ b) = k ⊗ (1 ⊗ b)` because `σ` fixes `K`. Then `piTensorSemilinear` and its multiplicativity lemmas give the algebra map `j`. On pure tensors, the Galois action sends the factor at `g⁻¹ τ` to the factor at `τ` by `x ⊗ a ↦ g x ⊗ a`. Since `g 1 = 1`, this is `j` of the permuted pure tensor.

**The twisted action is an action.** Write `φ_g(t) = g(t) · j(w_g)`.

- *Identity.* `φ_1` is the identity because `w_1 = 1`.
- *Semilinearity.* `φ_g` is `g`-semilinear because right multiplication is `N`-linear.
- *Composition.* `φ_g(φ_h(t)) = (gh)(t) · j(perm_g(w_h)) · j(w_g)`. By `twistUnit_conj`, `perm_g(w_h) = w_g w_h w_g⁻¹`, so this equals `(gh)(t) · j(w_g w_h) = φ_{gh}(t)`.

**Stability of the fixed space.**

- *Left.* For `d` in the descended algebra, `g(d x) j(w_g) = d · g(x) j(w_g)`.
- *Right.* `g(x · j(c)) · j(w_g) = g(x) · j(w_g c w_g⁻¹) · j(w_g) = g(x) · j(w_g) · j(c)`.

**Bijectivity.**

- *Injectivity.* The descended algebra of `L ⊗_K B` is central simple (`CentralSimple`, with the Library's scalar-extension results). `Cᵐᵒᵖ` is central simple as the opposite of a finite tensor power of central simple algebras. So the source is simple by the published `Langlands.CentralSimple.isSimpleRing_tensor` (Task 7532), and the homomorphism is injective.
- *Dimensions.* Galois descent for the twisted action (`GaloisDescent.SemilinearAction.descentEquiv`) gives `dim_K(fixed) = dim_N(⨂_σ (L ⊗ B)^σ) = (dim_K B)^|E|`. The source has dimension `(dim_K B)^|E| · (dim_K B)^|E|`. Equal dimensions give surjectivity.

## Sources and scope

The identity `Cor_{L/K}(Res_{L/K}[B]) = [L : K]·[B]` is the normalization requested by the task. For quadratic extensions it is M.-A. Knus, A. Merkurjev, M. Rost and J.-P. Tignol, *The Book of Involutions* (1998), Proposition (3.13)(5), printed p. 37 / PDF p. 60: `N_{K/F}(A_K) ∼ A ⊗_F A`. In their proof, on printed pp. 38–39 / PDF pp. 61–62, the Goldman element `g` of `A ⊗_F A` implements the flip of the two factors `A`. A unit built from it, `α + (g ⊗ 1)ι(α)`, intertwines the switch action with the scalar action by conjugation. The permutation units `w_g` play the role of the Goldman element here.

The argument here is an internal derivation. The algebra isomorphism holds for every finite `L/K` and finite Galois `N/K`. Its class interpretation needs the full-embedding condition above. That condition matches J. Tits, *Représentations linéaires irréductibles d'un groupe réductif sur un corps quelconque* (1971), §5.3, printed p. 208 / PDF p. 13. Tits tensors over the separable closure with one factor for each coset of `Gal(k_s/k₁)` in `Gal(k_s/k)`, so there are `[k₁ : k]` factors. The `K`-embeddings `L → N` correspond to these cosets exactly when `N` contains a normal closure of `L/K`, that is, when there are `[L : K]` of them. The permutation of the factors of `C` is untwisted by the permutation units of `PermUnits`. The descended algebra and `Cᵐᵒᵖ` then act on the twisted fixed space, and dimension counting gives the full endomorphism algebra.
