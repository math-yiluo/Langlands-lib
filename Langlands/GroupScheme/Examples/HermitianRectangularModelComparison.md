# Comparing a finite-source Hermitian presentation with the actual model

This is internal coordinate infrastructure for the final comparison in Task
5813. It uses actual two-sided inverse rectangular matrices, rather than an
assumed group-scheme identification. The finite source and target index types
may differ. Coefficients are arbitrary commutative rings, including the tensor
coefficient rings of test schemes.

For matrices `P : Matrix κ ι A` and `Q : Matrix ι κ A` with `PQ = 1` and
`QP = 1`, the coordinate change sends an invertible matrix `g` to `PgQ`. Its
inverse sends `h` to `QhP`. Both multiplication and the inverse identities
follow by matrix associativity and the two supplied inverse identities.
Mathlib's `Matrix.det_conj_of_mul_eq_one` proves determinant preservation for
these possibly different finite index types.

Write `M* = (M.map c.bar).transpose`. If `P* B P = J`, multiplying by `Q*`
and `Q` gives `Q* J Q = B`. Substitution in the full isometry equation gives
`(PgQ)* B (PgQ) = B` if and only if `g* J g = J`. This argument uses the full
pairing equation and works in every characteristic.

This module does not construct the quadratic extension or a Hermitian
presentation of an arbitrary group, and it does not compare split rank with
isotropic dimension. Those remain separate mathematical obligations.
