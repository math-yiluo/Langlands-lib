# Tensor descent of split algebras

This module shows that the tensor descent of a split central simple algebra is split. Let `φ : A →ₐ[L] Module.End L W` be an `L`-algebra homomorphism, where `W` is an `L`-algebra used only as an `L`-vector space.

- Factor by factor, the conjugates `A^σ` act on the conjugates `W^σ`. So `⨂_σ A^σ` acts `N`-linearly on `⨂_σ W^σ`, compatibly with the Galois actions.
- Therefore the descended algebra `corAlg K L N A` acts `K`-linearly on the descended space `corAlg K L N W`.
- When `A` is central simple of dimension `(dim_L W)^2`, this action is an isomorphism onto a full matrix algebra over `K`.

In particular `corAlg K L N (M_n(L))` is isomorphic to the matrix algebra `M_{n^e}(K)`, where `e = #(L →ₐ[K] N)`. The space `W = Fin n → L` is used as a commutative `L`-algebra, so its tensor product of conjugates is the ring `ConjTensor K L N W` with the Galois action of `Construction`.

There is no hypothesis on the characteristic or on infiniteness of `K`.

## Public declarations

Everything is in the namespace `Langlands.BrauerCorestriction`.

**The action.**

- `conjActTwist φ σ : Conj A σ →ₐ[Twist σ] Module.End (Twist σ) (Conj W σ)` is the `Twist σ`-algebra homomorphism `x ⊗ a ↦ x · (φ a ⊗ id)`. `conjAct φ σ : Conj A σ →ₗ[N] Module.End N (Conj W σ)` is the same map viewed `N`-linearly.
- `conjAct_tmul_tmul` computes `conjAct φ σ (x ⊗ a) (y ⊗ w) = (x y) ⊗ φ a w`.
- `conjAct_one` and `conjAct_mul` say that `conjAct` is multiplicative.
- `conjMap_conjAct` says that the action commutes with the Galois conjugations.
- `tensorAct K L N φ : ConjTensor K L N A →ₐ[N] Module.End N (ConjTensor K L N W)` is the factorwise action (`tensorAct_tprod_tprod`).
- `actMap_tensorAct_tprod` and `actMap_tensorAct` say that `tensorAct` intertwines the Galois actions: `g (t · v) = (g t) · (g v)`.
- `tensorAct_mem_corAlg` says that fixed elements act on fixed vectors and give fixed vectors.
- `corAct K L N φ : corAlg K L N A →ₐ[K] Module.End K (corAlg K L N W)` is the descended action (`corAct_apply`).

**The isomorphism.** Assume `L/K` finite, `N/K` finite Galois, `A` finite-dimensional central simple over `L`, `W` finite-dimensional and nontrivial over `L`, and `finrank L A = (finrank L W)^2`.

- `corActMatrix K L N φ` is `corAct` written in a chosen `K`-basis of `corAlg K L N W`. It is a `K`-algebra homomorphism to square matrices of size `finrank K (corAlg K L N W)`.
- `corActMatrix_bijective` says that it is bijective.
- `corAlgMatrixEquivOfRep K L N φ hdim` is the resulting `K`-algebra isomorphism between `corAlg K L N A` and that matrix algebra.

**Matrix algebras.**

- `finrank_corAlg_fin_fun` computes `finrank K (corAlg K L N (Fin n → L)) = n ^ #(L →ₐ[K] N)`.
- `corAlgMatrixEquiv K L N n` is a `K`-algebra isomorphism `corAlg K L N (Matrix (Fin n) (Fin n) L) ≃ₐ[K] Matrix (Fin (n ^ #(L →ₐ[K] N))) (Fin (n ^ #(L →ₐ[K] N))) K`, for `n ≠ 0`.

## Implemented proof

**The action.** `conjActTwist` is Mathlib's `Algebra.TensorProduct.lift` of the structure map of `Twist σ` into its endomorphism algebra and of `Module.End.baseChangeHom ∘ φ`. The images commute because scalars are central. Restricting scalars from `Twist σ` to `N` gives `conjAct`. Its `N`-linearity is the `Twist σ`-linearity of `conjActTwist`, since `N` acts on the conjugates through `Twist σ`. The value on pure tensors comes from `LinearMap.baseChange_tmul` and `Module.algebraMap_end_apply`.

The multilinear map `c ↦ PiTensorProduct.map (fun σ => conjAct φ σ (c σ))` (Mathlib's `mapMultilinear` composed with `conjAct`) preserves `1` and products of pure tensors (`PiTensorProduct.map_one`, `PiTensorProduct.map_mul`). So `PiTensorProduct.liftAlgHom` makes it the `N`-algebra homomorphism `tensorAct`.

**Equivariance.** On pure tensors, both sides of `actMap_tensorAct_tprod` are pure tensors indexed by the same source embeddings. They agree factorwise by `conjMap_conjAct`, which on `x ⊗ a` and `y ⊗ w` reduces to `g (x y) = g x · g y`. The general case is induction over scaled pure tensors in both arguments, using semilinearity of `actMap` and `N`-linearity of `tensorAct`.

**Descent.** For a fixed `d` and a fixed vector `v`, equivariance shows that `d · v` is fixed. `K`-linearity follows from `N`-linearity and the scalar tower. The homomorphism laws of `corAct` come from those of `tensorAct`.

**Bijectivity.** `corActMatrix` is `LinearMap.toMatrixAlgEquiv` for `Module.finBasis` composed with `corAct`. The freeness instance of the fixed subalgebra is supplied explicitly through `Module.Free.of_divisionRing`. The source `corAlg K L N A` is a simple ring (`isSimpleRing_corAlg`) and the matrix target is nontrivial, so the homomorphism is injective.

Its dimension is `(finrank L A)^e = (finrank L W)^{2e}` (`finrank_corAlg_eq_pow`). The matrix algebra has dimension `m^2`, where `m = finrank K (corAlg K L N W) = (finrank L W)^e`. The two agree, so injectivity gives surjectivity (`LinearMap.injective_iff_surjective_of_finrank_eq_finrank`).

**Matrix algebras.** For `M_n(L)`, take `W = Fin n → L` and `φ = Matrix.toLinAlgEquiv'`. Then `finrank L A = n^2` (`Module.finrank_matrix`). Reindex the matrix size by `finrank_corAlg_fin_fun` (`Matrix.reindexAlgEquiv`).

## Sources and scope

That corestriction sends the split class to the split class is part of the requested normalization: `Cor` must take split classes to split classes. Together with the multiplicativity of the descent, it gives compatibility with the matrix-stable Brauer equivalence. J. Tits, *Représentations linéaires irréductibles d'un groupe réductif sur un corps quelconque* (1971), §5.3, printed p. 208 / PDF p. 13, works only with division algebras, so this normalization does not appear there. The argument here is an internal derivation. The descended algebra of `M_n(L)` acts faithfully on the descended `K`-form of `⨂_σ (N ⊗_σ L^n)`, and dimension counting gives the full endomorphism algebra.
