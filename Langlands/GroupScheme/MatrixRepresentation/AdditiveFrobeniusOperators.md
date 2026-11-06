# Frobenius transforms of actual additive coefficient operators

This internal, derived construction starts with an actual representation of the
one-dimensional vector group over a field of prime characteristic `p`.
`frobeniusCoefficientOperator rho p e m` is the linear operator obtained by
raising every entry of the degree `m` coefficient matrix to `p ^ e`.

Postcomposition of the representation with the actual matrix Frobenius has
coefficient operator `frobeniusCoefficientOperator rho p e m` in degree
`p ^ e * m`. Every coefficient outside the degrees divisible by `p ^ e` is zero.
Thus its characteristic-power operators below height `e` vanish, and those at
indices `e + r` are the entrywise Frobenius transforms of the original
operators at `r`. This description includes transformation of the coefficient
field; the transformed operators need not equal the original operators.

The implementation evaluates the actual universal polynomial matrix at the
indeterminate and uses the existing affine matrix Frobenius formula. Mathlib's
`Polynomial.map_iterateFrobenius_expand` expresses its entrywise powers as
expansion of degrees followed by coefficient-field Frobenius. The polynomial
coefficient identities then give both formulas. The finite-height coefficient
criterion proves that the bounded fixed submodule at height `e` is the whole
space. Testing the standard basis vectors then proves that the actual affine
matrix is the identity at every scalar `t` satisfying `t ^ (p ^ e) = 0`.
Consequently every vector over every commutative test algebra is fixed there,
including over nonreduced algebras.

No infinitude or perfectness assumption is used. The actual additive
representation is supplied, and the module constructs no general root
subgroups, Frobenius-kernel group scheme, or Steinberg module. Its provenance is
the internal coefficient construction applied to the existing actual matrix
Frobenius, with all new claims proved directly from that construction.
