# Finite external products of Schwartz functions

This module supplies an internal construction for the equal-rank archimedean
factorization task. It does not prove the Rankin–Selberg factorization statement.
Its mathematical input is Mathlib's definition of `SchwartzMap` and its finite
product derivative estimate; it introduces no additional analytic assumption.

For a finite type `ι`, a family of real normed spaces `E i`, and complex-valued
Schwartz functions `f i` on these spaces,
`Langlands.Global.RankinSelbergGlobal.EqualSchwartzTensor.finiteTensor f`
is the Schwartz function on the finite dependent product with value

$$T(x)=\prod_{i:\iota} f_i(x_i).$$

The public lemma `finiteTensor_apply` records this formula. All index and domain
universes are arbitrary. No completeness or finite dimensionality is required.
The construction includes an empty index type, where the domain is the zero
space and the value is the empty product, one.

The implemented proof first bounds the norm of every derivative of a function
composed with a coordinate projection by the norm of that derivative of the
original function. The projection has operator norm at most one. It then bounds
`‖x‖^k` by `∏ i, (1 + ‖x i‖)^k`. Mathlib's
`norm_iteratedFDeriv_prod_le` expresses the derivative bound for a finite product
as a finite sum indexed by multisets of indices with total cardinality `n`.
For each summand, every derivative order is at most `n`, so
`SchwartzMap.one_add_le_sup_seminorm_apply` supplies a uniform bound for each
weighted local derivative. Multiplying these bounds and summing with the
nonnegative multinomial coefficients proves rapid decay. Smoothness follows by
composition with the continuous linear coordinate projections and finite
multiplication.

This is derived implementation infrastructure, rather than a translation of a
separate theorem in the literature. The application to the task is to assemble
arbitrary local real and complex Schwartz functions into a global archimedean
Schwartz function. Coordinate identifications, finite adelic factors, Fourier
normalization and Whittaker-integral factorization are separate obligations.
