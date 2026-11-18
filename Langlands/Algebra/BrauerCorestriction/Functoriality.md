# Functoriality of the tensor descent

This module makes the tensor-descent construction of `Langlands.Algebra.BrauerCorestriction.Construction` functorial in the `L`-algebra `A`:

- An `L`-algebra homomorphism `f : A →ₐ[L] B` induces a `K`-algebra homomorphism `corAlg K L N A →ₐ[K] corAlg K L N B`.
- An `L`-algebra isomorphism induces a `K`-algebra isomorphism.
- For two `L`-algebras `A` and `B`, it constructs the comparison homomorphism `corAlg A ⊗[K] corAlg B → corAlg (A ⊗[L] B)`.

No finiteness, Galois, central-simplicity, characteristic or infiniteness hypothesis is used. The fields and the algebras may lie in independent universes. The comparison homomorphism is shown to be an isomorphism in a later module, where central simplicity is available.

## Public declarations

Everything is in the namespace `Langlands.BrauerCorestriction`. Let `f : A →ₐ[L] B` and `σ : L →ₐ[K] N`.

**Factorwise maps.**

- `conjFun f σ : Conj A σ →ₗ[N] Conj B σ` sends `x ⊗ a` to `x ⊗ f a` (`conjFun_tmul`). It is `N`-linear, unital and multiplicative (`conjFun_one`, `conjFun_mul`).
- `conjFun_id_apply` and `conjFun_comp_apply` say that `conjFun` respects identities and composition.
- `conjMap_conjFun` says that `conjFun` commutes with the Galois conjugations `conjMap` of `Construction`.

**Tensor products of conjugates.**

- `funMap K L N f : ConjTensor K L N A →ₗ[N] ConjTensor K L N B` is `piTensorSemilinear (RingHom.id N)` of the maps `conjFun f σ`. On pure tensors it is `⨂ x_σ ↦ ⨂ conjFun f σ x_σ` (`funMap_tprod`).
- It is unital, multiplicative and `K`-linear (`funMap_one`, `funMap_mul`, `funMap_smul`), and it respects identities and composition (`funMap_id_apply`, `funMap_comp_apply`).
- `funMap_actMap` says that it commutes with the Galois actions `actMap`. Therefore it maps fixed vectors to fixed vectors (`funMap_mem_corAlg`).

**Descended algebras.**

- `corFun K L N f : corAlg K L N A →ₐ[K] corAlg K L N B` is the induced `K`-algebra homomorphism (`corFun_apply`).
- `corEquiv K L N f`, for `f : A ≃ₐ[L] B`, is the induced `K`-algebra isomorphism `corAlg K L N A ≃ₐ[K] corAlg K L N B`. So the descended algebra depends only on the isomorphism class of `A`.

**Tensor products of algebras.**

- `conjFun_includeLeft_commute` says that, in each conjugate of `A ⊗[L] B`, the images of `A^σ` and `B^σ` commute. These images come from the inclusions `a ↦ a ⊗ 1` and `b ↦ 1 ⊗ b`.
- `funMap_includeLeft_commute` is the same statement for the tensor products of conjugates.
- `corMul K L N A B : corAlg K L N A ⊗[K] corAlg K L N B →ₐ[K] corAlg K L N (A ⊗[L] B)` is the `K`-algebra homomorphism `v ⊗ w ↦ corFun includeLeft v * corFun includeRight w` (`corMul_tmul`).

## Implemented proof

`conjFun f σ` is the underlying map of `Algebra.TensorProduct.map (AlgHom.id L (Twist σ)) f`. Its `N`-linearity is an induction on tensors: the scalar acts on the left factor, which the map leaves unchanged. Multiplicativity is inherited from `Algebra.TensorProduct.map`. The identity, composition and conjugation lemmas are inductions on tensors that hold by definition on pure tensors.

`funMap` is `piTensorSemilinear` over the identity of `N`. Unitality and multiplicativity are `piTensorSemilinear_one` and `piTensorSemilinear_mul`. The identity and composition laws are `piTensorSemilinear_id` and `piTensorSemilinear_comp`.

**Equivariance.** Induct over scaled pure tensors. Both `actMap` and `funMap` are computed on pure tensors. The factorwise identity `conjMap_conjFun` finishes the proof, with no reindexing argument, because `funMap` does not move the index. `K`-linearity follows from `N`-linearity and the scalar tower `K → N`.

**Descended maps.** `corFun` restricts `funMap` to fixed vectors. Its algebra-homomorphism fields are checked on underlying elements. `corEquiv` is `AlgEquiv.ofAlgHom` of `corFun f` and `corFun f.symm`. The two composites are identities by `funMap_comp_apply` and `funMap_id_apply`.

**Commuting images.** On pure tensors `x ⊗ a` and `y ⊗ b`, both products equal `x y ⊗ (a ⊗ b)`. This uses `Algebra.TensorProduct.tmul_mul_tmul` and commutativity of the field `N`. Additivity extends this to all of `A^σ` and `B^σ`. For the tensor products, the products of scaled pure tensors are computed by `smul_tprod_mul_smul_tprod`, and the factors commute. `corMul` is Mathlib's `Algebra.TensorProduct.lift` of the two `corFun` maps with these commuting images.

## Sources and scope

The functoriality and multiplicativity of the tensor descent are standard properties of corestriction. They are needed to show compatibility with the matrix-stable Brauer equivalence and the group law. J. Tits, *Représentations linéaires irréductibles d'un groupe réductif sur un corps quelconque* (1971), §5.3, printed p. 208 / PDF p. 13, uses them implicitly when identifying the class of the fixed algebra with the cohomological corestriction. The constructions here are internal derivations on the actual tensor products of conjugates.
