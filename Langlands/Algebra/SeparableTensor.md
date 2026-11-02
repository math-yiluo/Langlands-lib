# Evaluation of a scalar extension at algebra homomorphisms

`Langlands.Algebra.SeparableTensor.embeddingEvaluation k K Ω` is the canonical
`Ω`-algebra map

```text
Ω ⊗[k] K → ((K →ₐ[k] Ω) → Ω),
c ⊗ x ↦ (σ ↦ c * σ(x)).
```

The construction only needs commutative semirings and the two `k`-algebra
structures. Neither finiteness nor separability is needed to define the map.
`embeddingEvaluation_tmul` fixes the coordinate convention.
`embeddingEvaluation_apply` identifies each coordinate with Mathlib's
`AlgHom.liftEquiv`; `embeddingEvaluation_linearMap` identifies its underlying
linear map with `LinearMap.liftBaseChangeEquiv`.

This is the explicit canonical map underlying the tensor decomposition used in
Milne, *Algebraic Groups* (2017), 2.61, printed p.59 / PDF p.75. That passage treats
finite étale algebras over a field and a splitting field containing their
conjugates. The semiring construction here is a derived extension of the formula,
using the universal property of the tensor product. It does not assert that this
map is bijective in this generality. Its finite separable field case is the
separate `EmbeddingEvaluationStatement`.

Source: registered `milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
