# Normalized products over reciprocal roots

This internal algebraic unit defines `reciprocalRootParameters P` as the
finite image under inversion of the complex polynomial's root multiset
with repetitions removed. If P has constant coefficient one, membership
is equivalent to a being nonzero and P having root a inverse. In
particular, none of the polynomial's roots is zero.

For a separable polynomial with constant coefficient one, the polynomial
is the product of `1 - a X` over this finite set. The proof uses splitting
over the complex numbers and separability to replace the root multiset
by its finite set without losing multiplicities. Each ordinary factor
`X - x` is rewritten as `(-x) (1 - x⁻¹ X)`. Evaluation at zero makes the
remaining overall constant equal to one. Inversion is injective, so
reindexing yields the asserted finite product.

These are derived polynomial facts from Mathlib's splitting and
separability theorems. No analytic continuation or representation
theoretic statement is assumed.
