# Determinant norms in product coordinates

Internal derived content. The determinant norm on a finite product `I → R`
is the product of its coordinates, for any commutative ring `R`, including
the zero ring, and any finite index set. The proof computes the multiplication
matrix in `Pi.basisFun` as a diagonal matrix and uses its determinant.

`tensorNorm_eq_prod` transports this formula along an `R`-algebra equivalence
`R ⊗_A B ≃ I → R`. It uses invariance of determinant norm under algebra
equivalence and the factor swap in the definition of `tensorNorm`.

Author: Worker 207.
