# Uniqueness of a normalized gamma decomposition

This is an internal algebraic statement for the proof of JPSS (1983),
Theorem (8.2), printed pages 444–448. It is a derived tool, not an assertion
attributed verbatim to that source.

Let `P`, `B`, `PD`, and `BD` be complex polynomials. Suppose that `P` and `B`
have constant coefficient one and no roots in the open disk of positive radius
`a`. Suppose that `PD` and `BD` have no roots in the open disk of positive radius
`b`. Let `δ` and `c` be nonzero complex units and `m` an integer, with
`‖δ‖ < a * b`.

If

`B(X) PD(δ/X) = c X^m P(X) BD(δ/X)`

as rational functions, then `P = B`. The stated identity is the cross
multiplication of two gamma decompositions up to a Laurent monomial.
No divisibility between `P` and `B` is assumed. No normalization of the dual
polynomials is needed. This file states the proposition and does not prove it.
