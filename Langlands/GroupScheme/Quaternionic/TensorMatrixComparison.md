# Scalar extension of matrices with involution

Authors: Worker 124.

Let `K` be a commutative ring, `D` a `K`-algebra with a possibly
noncommutative underlying ring, and `R` a commutative `K`-algebra. The finite
product tensor equivalence, applied to rows and columns, identifies
`R ⊗[K] Matrix m n D` with `Matrix m n (R ⊗[K] D)` as `K`-modules.
On a pure tensor it sends `r ⊗ M` to the matrix with entries `r ⊗ M i j`.
For square matrices this identification preserves identity and multiplication,
so it is an algebra equivalence. The coefficient rings and index types may
lie in independent universes.

Tensor induction proves that the equivalence commutes with every map of
coefficient `K`-algebras. If `D` carries a first-kind involution, the same
induction proves that the equivalence identifies the extended matrix adjoint
with the matrix adjoint of the extended involution. Consequently it identifies
the actual alternating subspaces: witnesses `a - adjoint(a)` pass through the
equivalence in both directions. No reducedness, field or characteristic
hypothesis is imposed.

This is an internal derivation using Mathlib's finite product tensor
equivalence and the Library involution definitions. It supplies coefficient
comparisons needed by the ambient hyperbolic isometry construction; it makes
no spin-cover or Kneser–Tits assertion.
