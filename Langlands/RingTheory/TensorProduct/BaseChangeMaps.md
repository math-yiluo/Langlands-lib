# Base-change maps on pure tensors

Mathlib's `LinearMap.tensorProduct R A M N` is the natural map from `A ⊗[R] (M →ₗ[R] N)` to `A`-linear maps `A ⊗[R] M → A ⊗[R] N`, and `LinearMap.tensorProductEnd` is its version for endomorphisms. On a pure tensor `a ⊗ f` both give `a • f.baseChange A`; this holds by unfolding the definitions. The two lemmas `LinearMap.tensorProduct_tmul` and `LinearMap.tensorProductEnd_tmul` state it as `simp` lemmas of high priority, so that a simplification reaches the `LinearMap.baseChange` form before it unfolds the lifting construction.

`Algebra.TensorProduct.lmul'_map_self` says that the multiplication map `A ⊗[R] A → A` commutes with an algebra map `f : A → C` applied to both factors. The proof is by induction on the tensor: on `a ⊗ b` both sides are `f a * f b`, and both sides are additive.
