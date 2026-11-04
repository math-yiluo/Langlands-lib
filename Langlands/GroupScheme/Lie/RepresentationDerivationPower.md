# Translation derivations on actual representation coefficients

This internal construction uses actual affine group points, representation
naturality, dual-number epsilon coefficients, and the global derivation of
left infinitesimal translation. It uses no external structural theorem.

For an affine group scheme over any commutative ring `R` and an actual matrix
representation of dimension `n`, `coordinateMatrix` is the representation
matrix at the universal point of the chosen coordinate algebra. Naturality
identifies its evaluation at every test point with that point's representation
matrix. Evaluation at identity is the identity matrix. The epsilon coefficients
at an actual identity-kernel point give its tangent matrix.

The representation matrix of a constant dual-number point is the entrywise
constant lift. Left infinitesimal translation of the universal point therefore
has matrix `(1 + epsilon*M) * U`, where `M` is the coefficient-extended tangent
matrix and `U` the universal matrix. Taking epsilon coefficients proves that
the translation derivation applied entrywise to `U` equals `M * U`.

Every base-linear map commutes with multiplication on the left by a matrix
whose entries lie in `R`. Applying this observation to the translation
derivation and using induction proves that its `m`th composition iterate
applied entrywise to `U` is the coefficient extension of the `m`th power of the
tangent matrix, multiplied by `U`. This includes `m = 0`.

For a natural prime `p` with `CharP R p`, and any `r : Nat`, the already
constructed derivation `D^(p^r)` can be evaluated at identity. This defines
`Lie.primePowerKernel G X p r`, an actual identity-kernel point over `R`.
When `r = 0` it recovers `X`. The general coefficient formula for evaluating
any global derivation at identity computes every representation differential
on the resulting Lie point. The iterate formula and augmentation of `U`
therefore prove, simultaneously for every actual finite matrix representation,
that its tangent matrix at `primePowerKernel G X p r` is the `p^r`th power of
its tangent matrix at `X`.

The base ring, group scheme, and affine test algebras inhabit one arbitrary
universe; the matrix index is `Fin n`, including `n = 0`. No field, smoothness,
finite type, reducedness, connectedness, perfection, or nontriviality assumption
is imposed. Primality and characteristic enter only for the prime-power
construction; the coefficient and ordinary iterate formulas hold over any
commutative base ring.

This module does not prove naturality of the constructed Lie powers under
scheme base change, a full restricted Lie algebra structure, semisimple
replacement, or Cartan generation.
