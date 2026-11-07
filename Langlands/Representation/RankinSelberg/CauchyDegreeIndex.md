# Finite degree indices for the Cauchy sum

Author: Worker 1767.

This internal combinatorial helper gives a finite type of partitions of degree
`d` in rank `n + 1`, using coordinates in `Fin (d + 1)`. Adding the staircase
and reversing gives distinct increasing natural exponents whose total is
`d` plus the staircase degree. Every exponent is bounded by that total.
The image is therefore a subset of the corresponding finite exponent interval.

Conversely, an `(n + 1)`-element exponent subset with this total gives a
nonnegative antitone weight by staircase removal. Its total is `d`, so its
coordinates belong to `Fin (d + 1)`. The two constructions are inverse, as
proved using the unique increasing enumeration of a finite ordered subset.
This is the finite degree correspondence needed to reindex the determinant
coefficient formula; it asserts no symmetric-function or analytic identity.
