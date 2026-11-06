# Centered segment gamma telescoping statement

This is an internal finite-product identity designed for the algebraic part of
JPSS (1983), Theorem (8.2). It is a derived formulation rather than a
transcription of a source assertion.

Write `f(a) = 1 - a X` and `k(i,j) = m+n-2i-2j`, with integer arithmetic.
For complex units `a,t`, the full polynomial is the product of
`f(a t^k(i,j))` over `0 ≤ i ≤ m` and `0 ≤ j ≤ n`. The boundary polynomial is
the product over its first row `i=0`.

For any finite set `A` of complex units, let `P` be the product of its full
polynomials, and `PD` the same product after replacing both `a` and `t` by
their inverses. Let `B` be the product of its boundary polynomials, and `BD`
the same boundary product after replacing only `a` by its inverse. Reflection
means the actual rational substitution `X ↦ t²/X`.

The proposition asserts the existence of a complex unit `c` and an integer `e`
such that

`B(X) / BD(t²/X) = c X^e P(X) / PD(t²/X)`.

The empty set is allowed. No size order between `m,n`, no absolute-value
condition on `a,t`, and no representation-theoretic factor existence are
assumed. The identity follows by reflecting linear factors, telescoping the
full product along the first index, and reversing the second index to
identify the remaining denominator with the reflected boundary product.
Applying it to Rankin–Selberg factors separately requires their reciprocal
parameters, dual inversion, and the appropriate spectral scale.
