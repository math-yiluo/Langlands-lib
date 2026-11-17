# Arbitrary scalar extension of augmented section jets

Let `R` be a commutative ring, let `A` be a commutative `R`-algebra, and
let `ε : A →ₐ[R] R` be an augmentation. For any commutative `R`-algebra
`S`, `baseChangeAugmentation ε S` evaluates `s ⊗ a` as
`s * algebraMap R S (ε a)`.

The kernel of this map is the extension of `ker ε` along the tensor
inclusion of `A`. The proof uses the surjectivity of the augmentation,
which has the algebra structure map as a section, and right exactness
of tensor products. The right tensor identity equivalence does not
change the kernel.

`baseChangeEquiv ε S n` is the resulting algebra equivalence
`S ⊗[R] (A / (ker ε)^(n+1)) ≃ₐ[S]
(S ⊗[R] A) / (ker (baseChangeAugmentation ε S))^(n+1)`.
The proof applies the imported tensor-product quotient equivalence
and the fact that extension of an ideal commutes with its powers.
Its formula on pure tensors sends `s ⊗ [a]` to `[s ⊗ a]`.
`baseChangeEquiv_truncate` proves compatibility with actual truncation.

This is an internal consequence of the imported tensor quotient and
right-exactness results. It requires no flatness, smoothness, finite
generation, or noetherian hypothesis, and the three rings can have
independent universes. A comparison with the coordinate algebra of
an actual base-changed group scheme is a separate geometric step.
