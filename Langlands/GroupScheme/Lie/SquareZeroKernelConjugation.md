# Conjugation and tangent evaluation in square-zero kernels

This internal construction concerns the actual point kernel of
`G(A) → G(A/I)`, where `G` is a group scheme over `Spec R`, `A` is an
`R`-algebra, and `I` is an actual ideal with `I² = 0`.

`kernelConjugation` is actual conjugation on this normal subgroup. For affine
`G`, its previously proved commutativity implies that conjugation by a kernel
point is trivial and that `kernelConjugation_eq_of_reduction_eq` holds: two
points with the same reduction induce exactly the same automorphism of the
kernel. These conclusions do not require smoothness or surjectivity of the
reduction map.

`tangentEvaluation I hI i` is the actual algebra map from `DualNumber A` to
`A` sending `(a,b)` to `a + b*i`, for `i ∈ I`. It is constructed by mapping
the formal infinitesimal module `A` to `I`, then using the previously constructed
collapse of `A ⊕ I`. Its action fixes constant points. The induced actual
`tangentPoint` sends the dual-number identity kernel into the kernel modulo
`I`. For affine `G`, `tangentPoint_derivation` states that its ideal-valued
coordinate derivation is the original tangent derivation multiplied by `i`.

`tangentPoint_adjoint` proves that evaluation of an actual adjoint tangent
vector is conjugation of the evaluated kernel point. The proof applies the
actual point functor to multiplication and inverses and uses the constant-point
formula. This formula makes no smoothness assumption.

The constructions and proofs are derived from the project's actual Lie-kernel,
coordinate, adjoint and square-zero extension APIs. They assert no nonaffine
coordinate comparison or global homomorphism lifting result.
